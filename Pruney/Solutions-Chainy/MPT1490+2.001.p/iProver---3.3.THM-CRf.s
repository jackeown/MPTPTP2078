%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:06 EST 2020

% Result     : Theorem 15.56s
% Output     : CNFRefutation 15.56s
% Verified   : 
% Statistics : Number of formulae       :  328 (46962 expanded)
%              Number of clauses        :  251 (12764 expanded)
%              Number of leaves         :   20 (9559 expanded)
%              Depth                    :   38
%              Number of atoms          : 1736 (321689 expanded)
%              Number of equality atoms :  743 (25665 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v17_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r4_lattice3(X1,X2,X0)
            <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <~> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <~> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f45])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ( ~ r3_lattice3(X1,k7_lattices(X1,sK5),a_2_0_lattice3(X0,X1))
          | ~ r4_lattice3(X1,sK5,X0) )
        & ( r3_lattice3(X1,k7_lattices(X1,sK5),a_2_0_lattice3(X0,X1))
          | r4_lattice3(X1,sK5,X0) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | ~ r4_lattice3(X1,X2,X0) )
            & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | r4_lattice3(X1,X2,X0) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r3_lattice3(sK4,k7_lattices(sK4,X2),a_2_0_lattice3(sK3,sK4))
            | ~ r4_lattice3(sK4,X2,sK3) )
          & ( r3_lattice3(sK4,k7_lattices(sK4,X2),a_2_0_lattice3(sK3,sK4))
            | r4_lattice3(sK4,X2,sK3) )
          & m1_subset_1(X2,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v17_lattices(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
      | ~ r4_lattice3(sK4,sK5,sK3) )
    & ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
      | r4_lattice3(sK4,sK5,sK3) )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v17_lattices(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f46,f48,f47])).

fof(f76,plain,
    ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | r4_lattice3(sK4,sK5,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X2)
        & v17_lattices(X2)
        & v10_lattices(X2)
        & ~ v2_struct_0(X2) )
     => ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & k7_lattices(X2,X3) = X0
              & m1_subset_1(X3,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & k7_lattices(X2,X4) = X0
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & k7_lattices(X2,X4) = X0
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & k7_lattices(X2,sK2(X0,X1,X2)) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & k7_lattices(X2,sK2(X0,X1,X2)) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ r2_hidden(X3,X1)
      | k7_lattices(X2,X3) != X0
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k7_lattices(X2,X3),a_2_0_lattice3(X1,X2))
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X2,sK2(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

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
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f51,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,
    ( ~ r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | ~ r4_lattice3(sK4,sK5,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              | ~ r3_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              | ~ r3_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_22,negated_conjecture,
    ( r4_lattice3(sK4,sK5,sK3)
    | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_510,negated_conjecture,
    ( r4_lattice3(sK4,sK5,sK3)
    | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1168,plain,
    ( r4_lattice3(sK4,sK5,sK3) = iProver_top
    | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k7_lattices(X2,X0),a_2_0_lattice3(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_515,plain,
    ( ~ r2_hidden(X0_51,X0_53)
    | r2_hidden(k7_lattices(X0_50,X0_51),a_2_0_lattice3(X0_53,X0_50))
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ v17_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v10_lattices(X0_50) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1163,plain,
    ( r2_hidden(X0_51,X0_53) != iProver_top
    | r2_hidden(k7_lattices(X0_50,X0_51),a_2_0_lattice3(X0_53,X0_50)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | m1_subset_1(k7_lattices(X0_50,X0_51),u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1150,plain,
    ( m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(k7_lattices(X0_50,X0_51),u1_struct_0(X0_50)) = iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_12,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_520,plain,
    ( ~ r3_lattice3(X0_50,X0_51,X0_53)
    | r1_lattices(X0_50,X0_51,X1_51)
    | ~ r2_hidden(X1_51,X0_53)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1158,plain,
    ( r3_lattice3(X0_50,X0_51,X0_53) != iProver_top
    | r1_lattices(X0_50,X0_51,X1_51) = iProver_top
    | r2_hidden(X1_51,X0_53) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_4262,plain,
    ( r3_lattice3(X0_50,X0_51,X0_53) != iProver_top
    | r1_lattices(X0_50,X0_51,k7_lattices(X0_50,X1_51)) = iProver_top
    | r2_hidden(k7_lattices(X0_50,X1_51),X0_53) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_1158])).

cnf(c_11670,plain,
    ( r3_lattice3(X0_50,X0_51,a_2_0_lattice3(X0_53,X0_50)) != iProver_top
    | r1_lattices(X0_50,X0_51,k7_lattices(X0_50,X1_51)) = iProver_top
    | r2_hidden(X1_51,X0_53) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_4262])).

cnf(c_45506,plain,
    ( r4_lattice3(sK4,sK5,sK3) = iProver_top
    | r1_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,X0_51)) = iProver_top
    | r2_hidden(X0_51,sK3) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1168,c_11670])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,plain,
    ( v10_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v17_lattices(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,plain,
    ( v17_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,plain,
    ( l3_lattices(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_554,plain,
    ( m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(k7_lattices(X0_50,X0_51),u1_struct_0(X0_50)) = iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_556,plain,
    ( m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_46547,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_51,sK3) != iProver_top
    | r1_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,X0_51)) = iProver_top
    | r4_lattice3(sK4,sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45506,c_28,c_29,c_30,c_31,c_32,c_556])).

cnf(c_46548,plain,
    ( r4_lattice3(sK4,sK5,sK3) = iProver_top
    | r1_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,X0_51)) = iProver_top
    | r2_hidden(X0_51,sK3) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_46547])).

cnf(c_5,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_527,plain,
    ( ~ r1_lattices(X0_50,X0_51,X1_51)
    | r3_lattices(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ v6_lattices(X0_50)
    | ~ v8_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v9_lattices(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1151,plain,
    ( r1_lattices(X0_50,X0_51,X1_51) != iProver_top
    | r3_lattices(X0_50,X0_51,X1_51) = iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v6_lattices(X0_50) != iProver_top
    | v8_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v9_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_2469,plain,
    ( r1_lattices(X0_50,X0_51,k7_lattices(X0_50,X1_51)) != iProver_top
    | r3_lattices(X0_50,X0_51,k7_lattices(X0_50,X1_51)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | v6_lattices(X0_50) != iProver_top
    | v8_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v9_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_1151])).

cnf(c_46560,plain,
    ( r4_lattice3(sK4,sK5,sK3) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,X0_51)) = iProver_top
    | r2_hidden(X0_51,sK3) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | v6_lattices(sK4) != iProver_top
    | v8_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v9_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_46548,c_2469])).

cnf(c_538,plain,
    ( ~ r1_lattices(X0_50,X0_51,X1_51)
    | r1_lattices(X0_50,X2_51,X3_51)
    | X2_51 != X0_51
    | X3_51 != X1_51 ),
    theory(equality)).

cnf(c_534,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_533,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1776,plain,
    ( X0_51 != X1_51
    | X1_51 = X0_51 ),
    inference(resolution,[status(thm)],[c_534,c_533])).

cnf(c_535,plain,
    ( X0_51 != X1_51
    | k7_lattices(X0_50,X0_51) = k7_lattices(X0_50,X1_51) ),
    theory(equality)).

cnf(c_2888,plain,
    ( X0_51 != X1_51
    | k7_lattices(X0_50,X1_51) = k7_lattices(X0_50,X0_51) ),
    inference(resolution,[status(thm)],[c_1776,c_535])).

cnf(c_7762,plain,
    ( ~ r1_lattices(X0_50,X0_51,k7_lattices(X1_50,X1_51))
    | r1_lattices(X0_50,X2_51,k7_lattices(X1_50,X3_51))
    | X2_51 != X0_51
    | X1_51 != X3_51 ),
    inference(resolution,[status(thm)],[c_538,c_2888])).

cnf(c_6339,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | r1_lattices(sK4,k7_lattices(sK4,sK5),X0_51)
    | ~ r2_hidden(X0_51,a_2_0_lattice3(sK3,sK4))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_520,c_510])).

cnf(c_555,plain,
    ( m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_6594,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | ~ r2_hidden(X0_51,a_2_0_lattice3(sK3,sK4))
    | r1_lattices(sK4,k7_lattices(sK4,sK5),X0_51)
    | r4_lattice3(sK4,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6339,c_27,c_24,c_23,c_555])).

cnf(c_6595,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | r1_lattices(sK4,k7_lattices(sK4,sK5),X0_51)
    | ~ r2_hidden(X0_51,a_2_0_lattice3(sK3,sK4))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_6594])).

cnf(c_27960,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | r1_lattices(sK4,X0_51,k7_lattices(X0_50,X1_51))
    | ~ r2_hidden(k7_lattices(X0_50,X2_51),a_2_0_lattice3(sK3,sK4))
    | ~ m1_subset_1(k7_lattices(X0_50,X2_51),u1_struct_0(sK4))
    | X2_51 != X1_51
    | X0_51 != k7_lattices(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_7762,c_6595])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | k7_lattices(X2,sK2(X0,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_513,plain,
    ( ~ r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50))
    | ~ v17_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v10_lattices(X0_50)
    | k7_lattices(X0_50,sK2(X0_51,X0_53,X0_50)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_540,plain,
    ( ~ r2_hidden(X0_51,X0_53)
    | r2_hidden(X1_51,X0_53)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_4670,plain,
    ( ~ r2_hidden(X0_51,X0_53)
    | ~ r2_hidden(X0_51,a_2_0_lattice3(X1_53,X0_50))
    | r2_hidden(k7_lattices(X0_50,sK2(X0_51,X1_53,X0_50)),X0_53)
    | ~ v17_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v10_lattices(X0_50) ),
    inference(resolution,[status(thm)],[c_513,c_540])).

cnf(c_28321,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | r1_lattices(sK4,X0_51,k7_lattices(X0_50,X1_51))
    | ~ r2_hidden(X2_51,a_2_0_lattice3(X0_53,X0_50))
    | ~ r2_hidden(X2_51,a_2_0_lattice3(sK3,sK4))
    | ~ m1_subset_1(k7_lattices(X0_50,sK2(X2_51,X0_53,X0_50)),u1_struct_0(sK4))
    | ~ v17_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v10_lattices(X0_50)
    | X0_51 != k7_lattices(sK4,sK5)
    | sK2(X2_51,X0_53,X0_50) != X1_51 ),
    inference(resolution,[status(thm)],[c_27960,c_4670])).

cnf(c_30318,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | r1_lattices(sK4,X0_51,k7_lattices(sK4,X1_51))
    | ~ r2_hidden(X2_51,a_2_0_lattice3(X0_53,sK4))
    | ~ r2_hidden(X2_51,a_2_0_lattice3(sK3,sK4))
    | ~ m1_subset_1(sK2(X2_51,X0_53,sK4),u1_struct_0(sK4))
    | ~ v17_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | X0_51 != k7_lattices(sK4,sK5)
    | sK2(X2_51,X0_53,sK4) != X1_51 ),
    inference(resolution,[status(thm)],[c_28321,c_528])).

cnf(c_46702,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | r1_lattices(sK4,X0_51,k7_lattices(sK4,X1_51))
    | ~ r2_hidden(X2_51,a_2_0_lattice3(X0_53,sK4))
    | ~ r2_hidden(X2_51,a_2_0_lattice3(sK3,sK4))
    | ~ m1_subset_1(sK2(X2_51,X0_53,sK4),u1_struct_0(sK4))
    | X0_51 != k7_lattices(sK4,sK5)
    | sK2(X2_51,X0_53,sK4) != X1_51 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30318,c_27,c_26,c_25,c_24])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_88,plain,
    ( v6_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_91,plain,
    ( v8_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_94,plain,
    ( ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | v9_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_518,plain,
    ( r4_lattice3(X0_50,X0_51,X0_53)
    | r2_hidden(sK1(X0_50,X0_51,X0_53),X0_53)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_585,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_15,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_517,plain,
    ( r4_lattice3(X0_50,X0_51,X0_53)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | m1_subset_1(sK1(X0_50,X0_51,X0_53),u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_588,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_13,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_519,plain,
    ( r4_lattice3(X0_50,X0_51,X0_53)
    | ~ r1_lattices(X0_50,sK1(X0_50,X0_51,X0_53),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_6,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_526,plain,
    ( r1_lattices(X0_50,X0_51,X1_51)
    | ~ r3_lattices(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ v6_lattices(X0_50)
    | ~ v8_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v9_lattices(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_10592,plain,
    ( r4_lattice3(X0_50,X0_51,X0_53)
    | ~ r3_lattices(X0_50,sK1(X0_50,X0_51,X0_53),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(sK1(X0_50,X0_51,X0_53),u1_struct_0(X0_50))
    | ~ v6_lattices(X0_50)
    | ~ v8_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v9_lattices(X0_50) ),
    inference(resolution,[status(thm)],[c_519,c_526])).

cnf(c_25471,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ r3_lattices(X0_50,sK1(X0_50,X0_51,X0_53),X0_51)
    | r4_lattice3(X0_50,X0_51,X0_53)
    | ~ v6_lattices(X0_50)
    | ~ v8_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v9_lattices(X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10592,c_517])).

cnf(c_25472,plain,
    ( r4_lattice3(X0_50,X0_51,X0_53)
    | ~ r3_lattices(X0_50,sK1(X0_50,X0_51,X0_53),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ v6_lattices(X0_50)
    | ~ v8_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v9_lattices(X0_50) ),
    inference(renaming,[status(thm)],[c_25471])).

cnf(c_25474,plain,
    ( r4_lattice3(sK4,sK5,sK3)
    | ~ r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v6_lattices(sK4)
    | ~ v8_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v9_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_25472])).

cnf(c_509,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1169,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_1161,plain,
    ( r4_lattice3(X0_50,X0_51,X0_53) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(sK1(X0_50,X0_51,X0_53),u1_struct_0(X0_50)) = iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ v17_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v10_lattices(X0_50)
    | k7_lattices(X0_50,k7_lattices(X0_50,X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1153,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,X0_51)) = X0_51
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_2562,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,sK1(X0_50,X0_51,X0_53))) = sK1(X0_50,X0_51,X0_53)
    | r4_lattice3(X0_50,X0_51,X0_53) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1153])).

cnf(c_9953,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,X0_53))) = sK1(sK4,sK5,X0_53)
    | r4_lattice3(sK4,sK5,X0_53) = iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_2562])).

cnf(c_10046,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,X0_53))) = sK1(sK4,sK5,X0_53)
    | r4_lattice3(sK4,sK5,X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9953,c_28,c_29,c_30,c_31])).

cnf(c_11,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_521,plain,
    ( r3_lattice3(X0_50,X0_51,X0_53)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | m1_subset_1(sK0(X0_50,X0_51,X0_53),u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1157,plain,
    ( r3_lattice3(X0_50,X0_51,X0_53) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(sK0(X0_50,X0_51,X0_53),u1_struct_0(X0_50)) = iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_2563,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,sK0(X0_50,X0_51,X0_53))) = sK0(X0_50,X0_51,X0_53)
    | r3_lattice3(X0_50,X0_51,X0_53) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_1153])).

cnf(c_10434,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,sK0(X0_50,k7_lattices(X0_50,X0_51),X0_53))) = sK0(X0_50,k7_lattices(X0_50,X0_51),X0_53)
    | r3_lattice3(X0_50,k7_lattices(X0_50,X0_51),X0_53) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_2563])).

cnf(c_21,negated_conjecture,
    ( ~ r4_lattice3(sK4,sK5,sK3)
    | ~ r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_511,negated_conjecture,
    ( ~ r4_lattice3(sK4,sK5,sK3)
    | ~ r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1167,plain,
    ( r4_lattice3(sK4,sK5,sK3) != iProver_top
    | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_19484,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | r4_lattice3(sK4,sK5,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10434,c_1167])).

cnf(c_19867,plain,
    ( r4_lattice3(sK4,sK5,sK3) != iProver_top
    | k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19484,c_28,c_29,c_30,c_31,c_32])).

cnf(c_19868,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | r4_lattice3(sK4,sK5,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_19867])).

cnf(c_19874,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
    | k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_10046,c_19868])).

cnf(c_1152,plain,
    ( r1_lattices(X0_50,X0_51,X1_51) = iProver_top
    | r3_lattices(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v6_lattices(X0_50) != iProver_top
    | v8_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v9_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_3832,plain,
    ( r1_lattices(sK4,X0_51,sK5) = iProver_top
    | r3_lattices(sK4,X0_51,sK5) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | v6_lattices(sK4) != iProver_top
    | v8_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v9_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1152])).

cnf(c_87,plain,
    ( v6_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_89,plain,
    ( v6_lattices(sK4) = iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_90,plain,
    ( v8_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_92,plain,
    ( v8_lattices(sK4) = iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_93,plain,
    ( l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | v9_lattices(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_95,plain,
    ( l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top
    | v9_lattices(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_5388,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r3_lattices(sK4,X0_51,sK5) != iProver_top
    | r1_lattices(sK4,X0_51,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3832,c_28,c_29,c_31,c_89,c_92,c_95])).

cnf(c_5389,plain,
    ( r1_lattices(sK4,X0_51,sK5) = iProver_top
    | r3_lattices(sK4,X0_51,sK5) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5388])).

cnf(c_5401,plain,
    ( r1_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_5389])).

cnf(c_5638,plain,
    ( r1_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5401,c_28,c_31])).

cnf(c_20201,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
    | r1_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))),sK5) = iProver_top
    | r3_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK5) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19874,c_5638])).

cnf(c_34,plain,
    ( r4_lattice3(sK4,sK5,sK3) != iProver_top
    | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_522,plain,
    ( r3_lattice3(X0_50,X0_51,X0_53)
    | r2_hidden(sK0(X0_50,X0_51,X0_53),X0_53)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1560,plain,
    ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4))
    | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_1561,plain,
    ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) = iProver_top
    | r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4)) = iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_512,plain,
    ( ~ r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50))
    | m1_subset_1(sK2(X0_51,X0_53,X0_50),u1_struct_0(X0_50))
    | ~ v17_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v10_lattices(X0_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1598,plain,
    ( ~ r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4))
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4))
    | ~ v17_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_1599,plain,
    ( r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4)) != iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) = iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1598])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50))
    | r2_hidden(sK2(X0_51,X0_53,X0_50),X0_53)
    | ~ v17_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v10_lattices(X0_50) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1597,plain,
    ( r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3)
    | ~ r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4))
    | ~ v17_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_1601,plain,
    ( r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) = iProver_top
    | r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_16,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_516,plain,
    ( ~ r4_lattice3(X0_50,X0_51,X0_53)
    | r1_lattices(X0_50,X1_51,X0_51)
    | ~ r2_hidden(X1_51,X0_53)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1800,plain,
    ( ~ r4_lattice3(X0_50,X0_51,sK3)
    | r1_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51)
    | ~ r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1801,plain,
    ( r4_lattice3(X0_50,X0_51,sK3) != iProver_top
    | r1_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) = iProver_top
    | r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(X0_50)) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_1803,plain,
    ( r4_lattice3(sK4,sK5,sK3) != iProver_top
    | r1_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) = iProver_top
    | r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_2155,plain,
    ( ~ r1_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51)
    | r3_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(X0_50))
    | ~ v6_lattices(X0_50)
    | ~ v8_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v9_lattices(X0_50) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_2156,plain,
    ( r1_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) != iProver_top
    | r3_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(X0_50)) != iProver_top
    | v6_lattices(X0_50) != iProver_top
    | v8_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v9_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2155])).

cnf(c_2158,plain,
    ( r1_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) != iProver_top
    | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) = iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v6_lattices(sK4) != iProver_top
    | v8_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v9_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_9,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_523,plain,
    ( r3_lattice3(X0_50,X0_51,X0_53)
    | ~ r1_lattices(X0_50,X0_51,sK0(X0_50,X0_51,X0_53))
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2678,plain,
    ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | ~ r1_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_2681,plain,
    ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) = iProver_top
    | r1_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2678])).

cnf(c_10049,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
    | r4_lattice3(sK4,sK5,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10046])).

cnf(c_1156,plain,
    ( r3_lattice3(X0_50,X0_51,X0_53) = iProver_top
    | r2_hidden(sK0(X0_50,X0_51,X0_53),X0_53) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_1165,plain,
    ( k7_lattices(X0_50,sK2(X0_51,X0_53,X0_50)) = X0_51
    | r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_2797,plain,
    ( k7_lattices(X0_50,sK2(sK0(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)),X0_53,X0_50)) = sK0(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50))
    | r3_lattice3(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X1_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X1_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_1165])).

cnf(c_16137,plain,
    ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | r4_lattice3(sK4,sK5,sK3) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2797,c_1167])).

cnf(c_17342,plain,
    ( r4_lattice3(sK4,sK5,sK3) != iProver_top
    | k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16137,c_28,c_29,c_30,c_31,c_32,c_556])).

cnf(c_17343,plain,
    ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | r4_lattice3(sK4,sK5,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_17342])).

cnf(c_17349,plain,
    ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_10046,c_17343])).

cnf(c_8,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_524,plain,
    ( ~ r3_lattices(X0_50,X0_51,X1_51)
    | r3_lattices(X0_50,k7_lattices(X0_50,X1_51),k7_lattices(X0_50,X0_51))
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ v17_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v10_lattices(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1154,plain,
    ( r3_lattices(X0_50,X0_51,X1_51) != iProver_top
    | r3_lattices(X0_50,k7_lattices(X0_50,X1_51),k7_lattices(X0_50,X0_51)) = iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_17560,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
    | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17349,c_1154])).

cnf(c_17774,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
    | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17560])).

cnf(c_17562,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_17349,c_1150])).

cnf(c_1557,plain,
    ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_1558,plain,
    ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) = iProver_top
    | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_18490,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
    | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17562,c_28,c_31,c_32,c_34,c_556,c_1558,c_10049])).

cnf(c_8672,plain,
    ( r1_lattices(X0_50,X0_51,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | ~ r3_lattices(X0_50,X0_51,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(X0_50))
    | ~ v6_lattices(X0_50)
    | ~ v8_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v9_lattices(X0_50) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_23001,plain,
    ( r1_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | ~ r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
    | ~ v6_lattices(sK4)
    | ~ v8_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v9_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_8672])).

cnf(c_23002,plain,
    ( r1_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != iProver_top
    | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | v6_lattices(sK4) != iProver_top
    | v8_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v9_lattices(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23001])).

cnf(c_27645,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20201,c_28,c_29,c_30,c_31,c_32,c_34,c_89,c_92,c_95,c_556,c_1561,c_1599,c_1601,c_1803,c_2158,c_2681,c_10049,c_17774,c_18490,c_23002])).

cnf(c_2564,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,k7_lattices(X0_50,X0_51))) = k7_lattices(X0_50,X0_51)
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_1153])).

cnf(c_3749,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,k7_lattices(X0_50,sK1(X0_50,X0_51,X0_53)))) = k7_lattices(X0_50,sK1(X0_50,X0_51,X0_53))
    | r4_lattice3(X0_50,X0_51,X0_53) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_2564])).

cnf(c_13891,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,X0_53)))) = k7_lattices(sK4,sK1(sK4,sK5,X0_53))
    | r4_lattice3(sK4,sK5,X0_53) = iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_3749])).

cnf(c_14292,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,X0_53)))) = k7_lattices(sK4,sK1(sK4,sK5,X0_53))
    | r4_lattice3(sK4,sK5,X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13891,c_28,c_29,c_30,c_31])).

cnf(c_19873,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_14292,c_19868])).

cnf(c_20441,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
    | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_19873,c_1150])).

cnf(c_14295,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
    | r4_lattice3(sK4,sK5,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14292])).

cnf(c_21129,plain,
    ( m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top
    | k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20441,c_28,c_31,c_32,c_34,c_556,c_1558,c_14295])).

cnf(c_21130,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
    | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_21129])).

cnf(c_2466,plain,
    ( r1_lattices(sK4,X0_51,sK5) != iProver_top
    | r3_lattices(sK4,X0_51,sK5) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | v6_lattices(sK4) != iProver_top
    | v8_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v9_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1151])).

cnf(c_3165,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r3_lattices(sK4,X0_51,sK5) = iProver_top
    | r1_lattices(sK4,X0_51,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2466,c_28,c_29,c_31,c_89,c_92,c_95])).

cnf(c_3166,plain,
    ( r1_lattices(sK4,X0_51,sK5) != iProver_top
    | r3_lattices(sK4,X0_51,sK5) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3165])).

cnf(c_21155,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
    | r1_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK5) != iProver_top
    | r3_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_21130,c_3166])).

cnf(c_17348,plain,
    ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_14292,c_17343])).

cnf(c_17806,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
    | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17348,c_1154])).

cnf(c_18020,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
    | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
    | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17806])).

cnf(c_24357,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21155,c_28,c_29,c_30,c_31,c_32,c_34,c_89,c_92,c_95,c_556,c_1561,c_1599,c_1601,c_1803,c_2158,c_2681,c_14295,c_18020,c_21130,c_23002])).

cnf(c_24367,plain,
    ( m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_24357,c_1150])).

cnf(c_24841,plain,
    ( m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24367,c_28,c_31])).

cnf(c_27652,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27645,c_24841])).

cnf(c_27674,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4))
    | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27652])).

cnf(c_24370,plain,
    ( r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top
    | r3_lattices(sK4,X0_51,k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))))) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
    | v6_lattices(sK4) != iProver_top
    | v8_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v9_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24357,c_2469])).

cnf(c_24448,plain,
    ( r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top
    | r3_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
    | v6_lattices(sK4) != iProver_top
    | v8_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v9_lattices(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24370,c_24357])).

cnf(c_38918,plain,
    ( m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r3_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24448,c_28,c_29,c_31,c_89,c_92,c_95])).

cnf(c_38919,plain,
    ( r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top
    | r3_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_38918])).

cnf(c_38924,plain,
    ( r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top
    | r3_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38919,c_27645])).

cnf(c_46561,plain,
    ( r4_lattice3(sK4,sK5,sK3) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46548,c_38924])).

cnf(c_1695,plain,
    ( ~ r4_lattice3(X0_50,X0_51,X0_53)
    | r1_lattices(X0_50,sK1(X1_50,X1_51,X0_53),X0_51)
    | ~ r2_hidden(sK1(X1_50,X1_51,X0_53),X0_53)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(sK1(X1_50,X1_51,X0_53),u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1696,plain,
    ( r4_lattice3(X0_50,X0_51,X0_53) != iProver_top
    | r1_lattices(X0_50,sK1(X1_50,X1_51,X0_53),X0_51) = iProver_top
    | r2_hidden(sK1(X1_50,X1_51,X0_53),X0_53) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(sK1(X1_50,X1_51,X0_53),u1_struct_0(X0_50)) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1695])).

cnf(c_1698,plain,
    ( r4_lattice3(sK4,sK5,sK3) != iProver_top
    | r1_lattices(sK4,sK1(sK4,sK5,sK3),sK5) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1696])).

cnf(c_3178,plain,
    ( r1_lattices(sK4,k7_lattices(sK4,X0_51),sK5) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_3166])).

cnf(c_3402,plain,
    ( r1_lattices(sK4,k7_lattices(sK4,X0_51),sK5) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3178,c_28,c_31])).

cnf(c_27691,plain,
    ( r1_lattices(sK4,sK1(sK4,sK5,sK3),sK5) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),sK5) = iProver_top
    | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27645,c_3402])).

cnf(c_27702,plain,
    ( r1_lattices(sK4,sK1(sK4,sK5,sK3),sK5) != iProver_top
    | r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5) = iProver_top
    | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27691,c_27645])).

cnf(c_24365,plain,
    ( r3_lattices(sK4,k7_lattices(sK4,X0_51),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),X0_51) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24357,c_1154])).

cnf(c_38541,plain,
    ( r3_lattices(sK4,k7_lattices(sK4,X0_51),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),X0_51) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24365,c_28,c_29,c_30,c_31])).

cnf(c_38547,plain,
    ( r3_lattices(sK4,sK1(sK4,sK5,sK3),X0_51) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,X0_51),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38541,c_27645])).

cnf(c_38553,plain,
    ( r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38547])).

cnf(c_47070,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46561,c_28,c_31,c_32,c_556,c_1698,c_27652,c_27702,c_38553])).

cnf(c_47071,plain,
    ( r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_47070])).

cnf(c_2561,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK5)) = sK5
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1153])).

cnf(c_564,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v17_lattices(sK4)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k7_lattices(sK4,k7_lattices(sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_3017,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2561,c_27,c_26,c_25,c_24,c_23,c_564])).

cnf(c_4536,plain,
    ( r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),X0_51) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3017,c_1154])).

cnf(c_9135,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),X0_51) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4536,c_28,c_29,c_30,c_31,c_32,c_556])).

cnf(c_9136,plain,
    ( r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),X0_51) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9135])).

cnf(c_47078,plain,
    ( r3_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),sK5) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_47071,c_9136])).

cnf(c_47083,plain,
    ( r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_47078,c_27645])).

cnf(c_47107,plain,
    ( r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_47083])).

cnf(c_47109,plain,
    ( r4_lattice3(sK4,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46702,c_27,c_26,c_24,c_23,c_88,c_91,c_94,c_585,c_588,c_25474,c_27674,c_47107])).

cnf(c_47111,plain,
    ( r4_lattice3(sK4,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47109])).

cnf(c_47436,plain,
    ( r4_lattice3(sK4,sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46560,c_47111])).

cnf(c_47443,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_47436,c_19868])).

cnf(c_47785,plain,
    ( r3_lattices(sK4,k7_lattices(sK4,X0_51),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_47443,c_1154])).

cnf(c_48090,plain,
    ( r3_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),sK5) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
    | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47785])).

cnf(c_1166,plain,
    ( r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50)) != iProver_top
    | m1_subset_1(sK2(X0_51,X0_53,X0_50),u1_struct_0(X0_50)) = iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_2974,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,sK2(X0_51,X0_53,X0_50))) = sK2(X0_51,X0_53,X0_50)
    | r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1153])).

cnf(c_6213,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)),X0_53,X0_50))) = sK2(sK0(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)),X0_53,X0_50)
    | r3_lattice3(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X1_50)) != iProver_top
    | v17_lattices(X0_50) != iProver_top
    | l3_lattices(X1_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v10_lattices(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_2974])).

cnf(c_41980,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)
    | r4_lattice3(sK4,sK5,sK3) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | v17_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v10_lattices(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6213,c_1167])).

cnf(c_43429,plain,
    ( r4_lattice3(sK4,sK5,sK3) != iProver_top
    | k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41980,c_28,c_29,c_30,c_31,c_32,c_556])).

cnf(c_43430,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)
    | r4_lattice3(sK4,sK5,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_43429])).

cnf(c_43431,plain,
    ( ~ r4_lattice3(sK4,sK5,sK3)
    | k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_43430])).

cnf(c_8829,plain,
    ( r1_lattices(X0_50,X0_51,X1_51)
    | ~ r1_lattices(X0_50,k7_lattices(sK4,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X2_51)
    | X1_51 != X2_51
    | X0_51 != k7_lattices(sK4,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_25082,plain,
    ( r1_lattices(X0_50,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51)
    | ~ r1_lattices(X0_50,k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X1_51)
    | X0_51 != X1_51
    | k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_8829])).

cnf(c_25083,plain,
    ( X0_51 != X1_51
    | k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)))
    | r1_lattices(X0_50,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51) = iProver_top
    | r1_lattices(X0_50,k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25082])).

cnf(c_25085,plain,
    ( k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)))
    | sK5 != sK5
    | r1_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),sK5) = iProver_top
    | r1_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25083])).

cnf(c_17344,plain,
    ( ~ r4_lattice3(sK4,sK5,sK3)
    | k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17343])).

cnf(c_2413,plain,
    ( X0_51 != X1_51
    | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != X1_51
    | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = X0_51 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_5564,plain,
    ( X0_51 != k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = X0_51
    | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_2413])).

cnf(c_13044,plain,
    ( k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = k7_lattices(X0_50,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)))
    | k7_lattices(X0_50,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_5564])).

cnf(c_13045,plain,
    ( k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)))
    | k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_13044])).

cnf(c_8790,plain,
    ( ~ m1_subset_1(k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4))
    | m1_subset_1(k7_lattices(sK4,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_8793,plain,
    ( m1_subset_1(k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(sK4)) = iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8790])).

cnf(c_8795,plain,
    ( m1_subset_1(k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(sK4)) = iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8793])).

cnf(c_5367,plain,
    ( ~ r1_lattices(X0_50,k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51)
    | r3_lattices(X0_50,k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(X0_50))
    | ~ v6_lattices(X0_50)
    | ~ v8_lattices(X0_50)
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50)
    | ~ v9_lattices(X0_50) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_5368,plain,
    ( r1_lattices(X0_50,k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51) != iProver_top
    | r3_lattices(X0_50,k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(X0_50)) != iProver_top
    | v6_lattices(X0_50) != iProver_top
    | v8_lattices(X0_50) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v9_lattices(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5367])).

cnf(c_5370,plain,
    ( r1_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),sK5) != iProver_top
    | r3_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),sK5) = iProver_top
    | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v6_lattices(sK4) != iProver_top
    | v8_lattices(sK4) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v9_lattices(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5368])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0_51,X0_52)
    | m1_subset_1(X1_51,X0_52)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_1593,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4))
    | X0_51 != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_3627,plain,
    ( ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4))
    | m1_subset_1(k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4))
    | k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_3633,plain,
    ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3627])).

cnf(c_2040,plain,
    ( X0_51 != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | k7_lattices(X0_50,X0_51) = k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_3084,plain,
    ( k7_lattices(X0_50,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
    | k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_3085,plain,
    ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
    | k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_3084])).

cnf(c_2956,plain,
    ( ~ r4_lattice3(X0_50,X0_51,sK3)
    | r1_lattices(X0_50,k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X0_51)
    | ~ r2_hidden(k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_2957,plain,
    ( r4_lattice3(X0_50,X0_51,sK3) != iProver_top
    | r1_lattices(X0_50,k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X0_51) = iProver_top
    | r2_hidden(k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(X0_50)) != iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2956])).

cnf(c_2959,plain,
    ( r4_lattice3(sK4,sK5,sK3) != iProver_top
    | r1_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK5) = iProver_top
    | r2_hidden(k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3) != iProver_top
    | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2957])).

cnf(c_2410,plain,
    ( k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_2412,plain,
    ( k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_2171,plain,
    ( ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(X0_50))
    | m1_subset_1(k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(X0_50))
    | ~ l3_lattices(X0_50)
    | v2_struct_0(X0_50) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_2172,plain,
    ( m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(X0_50)) = iProver_top
    | l3_lattices(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(c_2174,plain,
    ( m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) = iProver_top
    | l3_lattices(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2172])).

cnf(c_1789,plain,
    ( r2_hidden(X0_51,sK3)
    | ~ r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3)
    | X0_51 != sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_1976,plain,
    ( ~ r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3)
    | r2_hidden(k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3)
    | k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1789])).

cnf(c_1978,plain,
    ( k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)
    | r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) != iProver_top
    | r2_hidden(k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1976])).

cnf(c_1980,plain,
    ( k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)
    | r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) != iProver_top
    | r2_hidden(k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_550,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48090,c_47111,c_47109,c_43431,c_25085,c_23002,c_17344,c_13045,c_8795,c_5370,c_3633,c_3085,c_2959,c_2681,c_2412,c_2174,c_1980,c_1601,c_1561,c_1558,c_556,c_550,c_95,c_92,c_89,c_34,c_32,c_31,c_30,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:21:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.56/2.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.56/2.47  
% 15.56/2.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.56/2.47  
% 15.56/2.47  ------  iProver source info
% 15.56/2.47  
% 15.56/2.47  git: date: 2020-06-30 10:37:57 +0100
% 15.56/2.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.56/2.47  git: non_committed_changes: false
% 15.56/2.47  git: last_make_outside_of_git: false
% 15.56/2.47  
% 15.56/2.47  ------ 
% 15.56/2.47  ------ Parsing...
% 15.56/2.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.56/2.47  
% 15.56/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.56/2.47  
% 15.56/2.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.56/2.47  
% 15.56/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.47  ------ Proving...
% 15.56/2.47  ------ Problem Properties 
% 15.56/2.47  
% 15.56/2.47  
% 15.56/2.47  clauses                                 27
% 15.56/2.47  conjectures                             7
% 15.56/2.47  EPR                                     7
% 15.56/2.47  Horn                                    6
% 15.56/2.47  unary                                   5
% 15.56/2.47  binary                                  2
% 15.56/2.47  lits                                    126
% 15.56/2.47  lits eq                                 2
% 15.56/2.47  fd_pure                                 0
% 15.56/2.47  fd_pseudo                               0
% 15.56/2.47  fd_cond                                 0
% 15.56/2.47  fd_pseudo_cond                          0
% 15.56/2.47  AC symbols                              0
% 15.56/2.47  
% 15.56/2.47  ------ Input Options Time Limit: Unbounded
% 15.56/2.47  
% 15.56/2.47  
% 15.56/2.47  ------ 
% 15.56/2.47  Current options:
% 15.56/2.47  ------ 
% 15.56/2.47  
% 15.56/2.47  
% 15.56/2.47  
% 15.56/2.47  
% 15.56/2.47  ------ Proving...
% 15.56/2.47  
% 15.56/2.47  
% 15.56/2.47  % SZS status Theorem for theBenchmark.p
% 15.56/2.47  
% 15.56/2.47  % SZS output start CNFRefutation for theBenchmark.p
% 15.56/2.47  
% 15.56/2.47  fof(f9,conjecture,(
% 15.56/2.47    ! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f10,negated_conjecture,(
% 15.56/2.47    ~! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 15.56/2.47    inference(negated_conjecture,[],[f9])).
% 15.56/2.47  
% 15.56/2.47  fof(f30,plain,(
% 15.56/2.47    ? [X0,X1] : (? [X2] : ((r4_lattice3(X1,X2,X0) <~> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & m1_subset_1(X2,u1_struct_0(X1))) & (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)))),
% 15.56/2.47    inference(ennf_transformation,[],[f10])).
% 15.56/2.47  
% 15.56/2.47  fof(f31,plain,(
% 15.56/2.47    ? [X0,X1] : (? [X2] : ((r4_lattice3(X1,X2,X0) <~> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 15.56/2.47    inference(flattening,[],[f30])).
% 15.56/2.47  
% 15.56/2.47  fof(f45,plain,(
% 15.56/2.47    ? [X0,X1] : (? [X2] : (((~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0)) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r4_lattice3(X1,X2,X0))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 15.56/2.47    inference(nnf_transformation,[],[f31])).
% 15.56/2.47  
% 15.56/2.47  fof(f46,plain,(
% 15.56/2.47    ? [X0,X1] : (? [X2] : ((~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0)) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 15.56/2.47    inference(flattening,[],[f45])).
% 15.56/2.47  
% 15.56/2.47  fof(f48,plain,(
% 15.56/2.47    ( ! [X0,X1] : (? [X2] : ((~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0)) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) => ((~r3_lattice3(X1,k7_lattices(X1,sK5),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,sK5,X0)) & (r3_lattice3(X1,k7_lattices(X1,sK5),a_2_0_lattice3(X0,X1)) | r4_lattice3(X1,sK5,X0)) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 15.56/2.47    introduced(choice_axiom,[])).
% 15.56/2.47  
% 15.56/2.47  fof(f47,plain,(
% 15.56/2.47    ? [X0,X1] : (? [X2] : ((~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0)) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (? [X2] : ((~r3_lattice3(sK4,k7_lattices(sK4,X2),a_2_0_lattice3(sK3,sK4)) | ~r4_lattice3(sK4,X2,sK3)) & (r3_lattice3(sK4,k7_lattices(sK4,X2),a_2_0_lattice3(sK3,sK4)) | r4_lattice3(sK4,X2,sK3)) & m1_subset_1(X2,u1_struct_0(sK4))) & l3_lattices(sK4) & v17_lattices(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 15.56/2.47    introduced(choice_axiom,[])).
% 15.56/2.47  
% 15.56/2.47  fof(f49,plain,(
% 15.56/2.47    ((~r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) | ~r4_lattice3(sK4,sK5,sK3)) & (r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) | r4_lattice3(sK4,sK5,sK3)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v17_lattices(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 15.56/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f46,f48,f47])).
% 15.56/2.47  
% 15.56/2.47  fof(f76,plain,(
% 15.56/2.47    r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) | r4_lattice3(sK4,sK5,sK3)),
% 15.56/2.47    inference(cnf_transformation,[],[f49])).
% 15.56/2.47  
% 15.56/2.47  fof(f8,axiom,(
% 15.56/2.47    ! [X0,X1,X2] : ((l3_lattices(X2) & v17_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) => (r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f28,plain,(
% 15.56/2.47    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))) | (~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)))),
% 15.56/2.47    inference(ennf_transformation,[],[f8])).
% 15.56/2.47  
% 15.56/2.47  fof(f29,plain,(
% 15.56/2.47    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 15.56/2.47    inference(flattening,[],[f28])).
% 15.56/2.47  
% 15.56/2.47  fof(f41,plain,(
% 15.56/2.47    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 15.56/2.47    inference(nnf_transformation,[],[f29])).
% 15.56/2.47  
% 15.56/2.47  fof(f42,plain,(
% 15.56/2.47    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X4] : (r2_hidden(X4,X1) & k7_lattices(X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 15.56/2.47    inference(rectify,[],[f41])).
% 15.56/2.47  
% 15.56/2.47  fof(f43,plain,(
% 15.56/2.47    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & k7_lattices(X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & k7_lattices(X2,sK2(X0,X1,X2)) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))))),
% 15.56/2.47    introduced(choice_axiom,[])).
% 15.56/2.47  
% 15.56/2.47  fof(f44,plain,(
% 15.56/2.47    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & k7_lattices(X2,sK2(X0,X1,X2)) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 15.56/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 15.56/2.47  
% 15.56/2.47  fof(f70,plain,(
% 15.56/2.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f44])).
% 15.56/2.47  
% 15.56/2.47  fof(f78,plain,(
% 15.56/2.47    ( ! [X2,X3,X1] : (r2_hidden(k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 15.56/2.47    inference(equality_resolution,[],[f70])).
% 15.56/2.47  
% 15.56/2.47  fof(f2,axiom,(
% 15.56/2.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f16,plain,(
% 15.56/2.47    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.56/2.47    inference(ennf_transformation,[],[f2])).
% 15.56/2.47  
% 15.56/2.47  fof(f17,plain,(
% 15.56/2.47    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(flattening,[],[f16])).
% 15.56/2.47  
% 15.56/2.47  fof(f54,plain,(
% 15.56/2.47    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f17])).
% 15.56/2.47  
% 15.56/2.47  fof(f6,axiom,(
% 15.56/2.47    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f24,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.56/2.47    inference(ennf_transformation,[],[f6])).
% 15.56/2.47  
% 15.56/2.47  fof(f25,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(flattening,[],[f24])).
% 15.56/2.47  
% 15.56/2.47  fof(f33,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(nnf_transformation,[],[f25])).
% 15.56/2.47  
% 15.56/2.47  fof(f34,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(rectify,[],[f33])).
% 15.56/2.47  
% 15.56/2.47  fof(f35,plain,(
% 15.56/2.47    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 15.56/2.47    introduced(choice_axiom,[])).
% 15.56/2.47  
% 15.56/2.47  fof(f36,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 15.56/2.47  
% 15.56/2.47  fof(f59,plain,(
% 15.56/2.47    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f36])).
% 15.56/2.47  
% 15.56/2.47  fof(f71,plain,(
% 15.56/2.47    ~v2_struct_0(sK4)),
% 15.56/2.47    inference(cnf_transformation,[],[f49])).
% 15.56/2.47  
% 15.56/2.47  fof(f72,plain,(
% 15.56/2.47    v10_lattices(sK4)),
% 15.56/2.47    inference(cnf_transformation,[],[f49])).
% 15.56/2.47  
% 15.56/2.47  fof(f73,plain,(
% 15.56/2.47    v17_lattices(sK4)),
% 15.56/2.47    inference(cnf_transformation,[],[f49])).
% 15.56/2.47  
% 15.56/2.47  fof(f74,plain,(
% 15.56/2.47    l3_lattices(sK4)),
% 15.56/2.47    inference(cnf_transformation,[],[f49])).
% 15.56/2.47  
% 15.56/2.47  fof(f75,plain,(
% 15.56/2.47    m1_subset_1(sK5,u1_struct_0(sK4))),
% 15.56/2.47    inference(cnf_transformation,[],[f49])).
% 15.56/2.47  
% 15.56/2.47  fof(f3,axiom,(
% 15.56/2.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f18,plain,(
% 15.56/2.47    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 15.56/2.47    inference(ennf_transformation,[],[f3])).
% 15.56/2.47  
% 15.56/2.47  fof(f19,plain,(
% 15.56/2.47    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(flattening,[],[f18])).
% 15.56/2.47  
% 15.56/2.47  fof(f32,plain,(
% 15.56/2.47    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(nnf_transformation,[],[f19])).
% 15.56/2.47  
% 15.56/2.47  fof(f56,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f32])).
% 15.56/2.47  
% 15.56/2.47  fof(f68,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (k7_lattices(X2,sK2(X0,X1,X2)) = X0 | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f44])).
% 15.56/2.47  
% 15.56/2.47  fof(f1,axiom,(
% 15.56/2.47    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f11,plain,(
% 15.56/2.47    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.56/2.47    inference(pure_predicate_removal,[],[f1])).
% 15.56/2.47  
% 15.56/2.47  fof(f12,plain,(
% 15.56/2.47    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.56/2.47    inference(pure_predicate_removal,[],[f11])).
% 15.56/2.47  
% 15.56/2.47  fof(f13,plain,(
% 15.56/2.47    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 15.56/2.47    inference(pure_predicate_removal,[],[f12])).
% 15.56/2.47  
% 15.56/2.47  fof(f14,plain,(
% 15.56/2.47    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 15.56/2.47    inference(ennf_transformation,[],[f13])).
% 15.56/2.47  
% 15.56/2.47  fof(f15,plain,(
% 15.56/2.47    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 15.56/2.47    inference(flattening,[],[f14])).
% 15.56/2.47  
% 15.56/2.47  fof(f51,plain,(
% 15.56/2.47    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f15])).
% 15.56/2.47  
% 15.56/2.47  fof(f52,plain,(
% 15.56/2.47    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f15])).
% 15.56/2.47  
% 15.56/2.47  fof(f53,plain,(
% 15.56/2.47    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f15])).
% 15.56/2.47  
% 15.56/2.47  fof(f7,axiom,(
% 15.56/2.47    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f26,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.56/2.47    inference(ennf_transformation,[],[f7])).
% 15.56/2.47  
% 15.56/2.47  fof(f27,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(flattening,[],[f26])).
% 15.56/2.47  
% 15.56/2.47  fof(f37,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(nnf_transformation,[],[f27])).
% 15.56/2.47  
% 15.56/2.47  fof(f38,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(rectify,[],[f37])).
% 15.56/2.47  
% 15.56/2.47  fof(f39,plain,(
% 15.56/2.47    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 15.56/2.47    introduced(choice_axiom,[])).
% 15.56/2.47  
% 15.56/2.47  fof(f40,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 15.56/2.47  
% 15.56/2.47  fof(f65,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f40])).
% 15.56/2.47  
% 15.56/2.47  fof(f64,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f40])).
% 15.56/2.47  
% 15.56/2.47  fof(f66,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f40])).
% 15.56/2.47  
% 15.56/2.47  fof(f55,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f32])).
% 15.56/2.47  
% 15.56/2.47  fof(f4,axiom,(
% 15.56/2.47    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f20,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 15.56/2.47    inference(ennf_transformation,[],[f4])).
% 15.56/2.47  
% 15.56/2.47  fof(f21,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(flattening,[],[f20])).
% 15.56/2.47  
% 15.56/2.47  fof(f57,plain,(
% 15.56/2.47    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f21])).
% 15.56/2.47  
% 15.56/2.47  fof(f60,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f36])).
% 15.56/2.47  
% 15.56/2.47  fof(f77,plain,(
% 15.56/2.47    ~r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) | ~r4_lattice3(sK4,sK5,sK3)),
% 15.56/2.47    inference(cnf_transformation,[],[f49])).
% 15.56/2.47  
% 15.56/2.47  fof(f61,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f36])).
% 15.56/2.47  
% 15.56/2.47  fof(f67,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f44])).
% 15.56/2.47  
% 15.56/2.47  fof(f69,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f44])).
% 15.56/2.47  
% 15.56/2.47  fof(f63,plain,(
% 15.56/2.47    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f40])).
% 15.56/2.47  
% 15.56/2.47  fof(f62,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f36])).
% 15.56/2.47  
% 15.56/2.47  fof(f5,axiom,(
% 15.56/2.47    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 15.56/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.47  
% 15.56/2.47  fof(f22,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) | ~r3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 15.56/2.47    inference(ennf_transformation,[],[f5])).
% 15.56/2.47  
% 15.56/2.47  fof(f23,plain,(
% 15.56/2.47    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.56/2.47    inference(flattening,[],[f22])).
% 15.56/2.47  
% 15.56/2.47  fof(f58,plain,(
% 15.56/2.47    ( ! [X2,X0,X1] : (r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.56/2.47    inference(cnf_transformation,[],[f23])).
% 15.56/2.47  
% 15.56/2.47  cnf(c_22,negated_conjecture,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.47      inference(cnf_transformation,[],[f76]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_510,negated_conjecture,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_22]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1168,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) = iProver_top
% 15.56/2.47      | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_17,plain,
% 15.56/2.47      ( ~ r2_hidden(X0,X1)
% 15.56/2.47      | r2_hidden(k7_lattices(X2,X0),a_2_0_lattice3(X1,X2))
% 15.56/2.47      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 15.56/2.47      | ~ v17_lattices(X2)
% 15.56/2.47      | ~ l3_lattices(X2)
% 15.56/2.47      | v2_struct_0(X2)
% 15.56/2.47      | ~ v10_lattices(X2) ),
% 15.56/2.47      inference(cnf_transformation,[],[f78]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_515,plain,
% 15.56/2.47      ( ~ r2_hidden(X0_51,X0_53)
% 15.56/2.47      | r2_hidden(k7_lattices(X0_50,X0_51),a_2_0_lattice3(X0_53,X0_50))
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ v17_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v10_lattices(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_17]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1163,plain,
% 15.56/2.47      ( r2_hidden(X0_51,X0_53) != iProver_top
% 15.56/2.47      | r2_hidden(k7_lattices(X0_50,X0_51),a_2_0_lattice3(X0_53,X0_50)) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_4,plain,
% 15.56/2.47      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.56/2.47      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 15.56/2.47      | ~ l3_lattices(X1)
% 15.56/2.47      | v2_struct_0(X1) ),
% 15.56/2.47      inference(cnf_transformation,[],[f54]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_528,plain,
% 15.56/2.47      ( ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | m1_subset_1(k7_lattices(X0_50,X0_51),u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_4]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1150,plain,
% 15.56/2.47      ( m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(k7_lattices(X0_50,X0_51),u1_struct_0(X0_50)) = iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_12,plain,
% 15.56/2.47      ( ~ r3_lattice3(X0,X1,X2)
% 15.56/2.47      | r1_lattices(X0,X1,X3)
% 15.56/2.47      | ~ r2_hidden(X3,X2)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f59]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_520,plain,
% 15.56/2.47      ( ~ r3_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | r1_lattices(X0_50,X0_51,X1_51)
% 15.56/2.47      | ~ r2_hidden(X1_51,X0_53)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_12]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1158,plain,
% 15.56/2.47      ( r3_lattice3(X0_50,X0_51,X0_53) != iProver_top
% 15.56/2.47      | r1_lattices(X0_50,X0_51,X1_51) = iProver_top
% 15.56/2.47      | r2_hidden(X1_51,X0_53) != iProver_top
% 15.56/2.47      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_4262,plain,
% 15.56/2.47      ( r3_lattice3(X0_50,X0_51,X0_53) != iProver_top
% 15.56/2.47      | r1_lattices(X0_50,X0_51,k7_lattices(X0_50,X1_51)) = iProver_top
% 15.56/2.47      | r2_hidden(k7_lattices(X0_50,X1_51),X0_53) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1150,c_1158]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_11670,plain,
% 15.56/2.47      ( r3_lattice3(X0_50,X0_51,a_2_0_lattice3(X0_53,X0_50)) != iProver_top
% 15.56/2.47      | r1_lattices(X0_50,X0_51,k7_lattices(X0_50,X1_51)) = iProver_top
% 15.56/2.47      | r2_hidden(X1_51,X0_53) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1163,c_4262]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_45506,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) = iProver_top
% 15.56/2.47      | r1_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,X0_51)) = iProver_top
% 15.56/2.47      | r2_hidden(X0_51,sK3) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | v17_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1168,c_11670]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_27,negated_conjecture,
% 15.56/2.47      ( ~ v2_struct_0(sK4) ),
% 15.56/2.47      inference(cnf_transformation,[],[f71]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_28,plain,
% 15.56/2.47      ( v2_struct_0(sK4) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_26,negated_conjecture,
% 15.56/2.47      ( v10_lattices(sK4) ),
% 15.56/2.47      inference(cnf_transformation,[],[f72]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_29,plain,
% 15.56/2.47      ( v10_lattices(sK4) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_25,negated_conjecture,
% 15.56/2.47      ( v17_lattices(sK4) ),
% 15.56/2.47      inference(cnf_transformation,[],[f73]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_30,plain,
% 15.56/2.47      ( v17_lattices(sK4) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_24,negated_conjecture,
% 15.56/2.47      ( l3_lattices(sK4) ),
% 15.56/2.47      inference(cnf_transformation,[],[f74]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_31,plain,
% 15.56/2.47      ( l3_lattices(sK4) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_23,negated_conjecture,
% 15.56/2.47      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 15.56/2.47      inference(cnf_transformation,[],[f75]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_32,plain,
% 15.56/2.47      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_554,plain,
% 15.56/2.47      ( m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(k7_lattices(X0_50,X0_51),u1_struct_0(X0_50)) = iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_556,plain,
% 15.56/2.47      ( m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) = iProver_top
% 15.56/2.47      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_554]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_46547,plain,
% 15.56/2.47      ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | r2_hidden(X0_51,sK3) != iProver_top
% 15.56/2.47      | r1_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,X0_51)) = iProver_top
% 15.56/2.47      | r4_lattice3(sK4,sK5,sK3) = iProver_top ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_45506,c_28,c_29,c_30,c_31,c_32,c_556]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_46548,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) = iProver_top
% 15.56/2.47      | r1_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,X0_51)) = iProver_top
% 15.56/2.47      | r2_hidden(X0_51,sK3) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.47      inference(renaming,[status(thm)],[c_46547]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_5,plain,
% 15.56/2.47      ( ~ r1_lattices(X0,X1,X2)
% 15.56/2.47      | r3_lattices(X0,X1,X2)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.56/2.47      | ~ v6_lattices(X0)
% 15.56/2.47      | ~ v8_lattices(X0)
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0)
% 15.56/2.47      | ~ v9_lattices(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f56]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_527,plain,
% 15.56/2.47      ( ~ r1_lattices(X0_50,X0_51,X1_51)
% 15.56/2.47      | r3_lattices(X0_50,X0_51,X1_51)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ v6_lattices(X0_50)
% 15.56/2.47      | ~ v8_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v9_lattices(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_5]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1151,plain,
% 15.56/2.47      ( r1_lattices(X0_50,X0_51,X1_51) != iProver_top
% 15.56/2.47      | r3_lattices(X0_50,X0_51,X1_51) = iProver_top
% 15.56/2.47      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v6_lattices(X0_50) != iProver_top
% 15.56/2.47      | v8_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v9_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2469,plain,
% 15.56/2.47      ( r1_lattices(X0_50,X0_51,k7_lattices(X0_50,X1_51)) != iProver_top
% 15.56/2.47      | r3_lattices(X0_50,X0_51,k7_lattices(X0_50,X1_51)) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v6_lattices(X0_50) != iProver_top
% 15.56/2.47      | v8_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v9_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1150,c_1151]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_46560,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) = iProver_top
% 15.56/2.47      | r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,X0_51)) = iProver_top
% 15.56/2.47      | r2_hidden(X0_51,sK3) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | v6_lattices(sK4) != iProver_top
% 15.56/2.47      | v8_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v9_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_46548,c_2469]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_538,plain,
% 15.56/2.47      ( ~ r1_lattices(X0_50,X0_51,X1_51)
% 15.56/2.47      | r1_lattices(X0_50,X2_51,X3_51)
% 15.56/2.47      | X2_51 != X0_51
% 15.56/2.47      | X3_51 != X1_51 ),
% 15.56/2.47      theory(equality) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_534,plain,
% 15.56/2.47      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 15.56/2.47      theory(equality) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_533,plain,( X0_51 = X0_51 ),theory(equality) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1776,plain,
% 15.56/2.47      ( X0_51 != X1_51 | X1_51 = X0_51 ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_534,c_533]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_535,plain,
% 15.56/2.47      ( X0_51 != X1_51
% 15.56/2.47      | k7_lattices(X0_50,X0_51) = k7_lattices(X0_50,X1_51) ),
% 15.56/2.47      theory(equality) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2888,plain,
% 15.56/2.47      ( X0_51 != X1_51
% 15.56/2.47      | k7_lattices(X0_50,X1_51) = k7_lattices(X0_50,X0_51) ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_1776,c_535]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_7762,plain,
% 15.56/2.47      ( ~ r1_lattices(X0_50,X0_51,k7_lattices(X1_50,X1_51))
% 15.56/2.47      | r1_lattices(X0_50,X2_51,k7_lattices(X1_50,X3_51))
% 15.56/2.47      | X2_51 != X0_51
% 15.56/2.47      | X1_51 != X3_51 ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_538,c_2888]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_6339,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r1_lattices(sK4,k7_lattices(sK4,sK5),X0_51)
% 15.56/2.47      | ~ r2_hidden(X0_51,a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 15.56/2.47      | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4) ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_520,c_510]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_555,plain,
% 15.56/2.47      ( m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
% 15.56/2.47      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_528]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_6594,plain,
% 15.56/2.47      ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 15.56/2.47      | ~ r2_hidden(X0_51,a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | r1_lattices(sK4,k7_lattices(sK4,sK5),X0_51)
% 15.56/2.47      | r4_lattice3(sK4,sK5,sK3) ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_6339,c_27,c_24,c_23,c_555]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_6595,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r1_lattices(sK4,k7_lattices(sK4,sK5),X0_51)
% 15.56/2.47      | ~ r2_hidden(X0_51,a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(sK4)) ),
% 15.56/2.47      inference(renaming,[status(thm)],[c_6594]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_27960,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r1_lattices(sK4,X0_51,k7_lattices(X0_50,X1_51))
% 15.56/2.47      | ~ r2_hidden(k7_lattices(X0_50,X2_51),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ m1_subset_1(k7_lattices(X0_50,X2_51),u1_struct_0(sK4))
% 15.56/2.47      | X2_51 != X1_51
% 15.56/2.47      | X0_51 != k7_lattices(sK4,sK5) ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_7762,c_6595]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_19,plain,
% 15.56/2.47      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 15.56/2.47      | ~ v17_lattices(X2)
% 15.56/2.47      | ~ l3_lattices(X2)
% 15.56/2.47      | v2_struct_0(X2)
% 15.56/2.47      | ~ v10_lattices(X2)
% 15.56/2.47      | k7_lattices(X2,sK2(X0,X1,X2)) = X0 ),
% 15.56/2.47      inference(cnf_transformation,[],[f68]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_513,plain,
% 15.56/2.47      ( ~ r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50))
% 15.56/2.47      | ~ v17_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v10_lattices(X0_50)
% 15.56/2.47      | k7_lattices(X0_50,sK2(X0_51,X0_53,X0_50)) = X0_51 ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_19]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_540,plain,
% 15.56/2.47      ( ~ r2_hidden(X0_51,X0_53)
% 15.56/2.47      | r2_hidden(X1_51,X0_53)
% 15.56/2.47      | X1_51 != X0_51 ),
% 15.56/2.47      theory(equality) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_4670,plain,
% 15.56/2.47      ( ~ r2_hidden(X0_51,X0_53)
% 15.56/2.47      | ~ r2_hidden(X0_51,a_2_0_lattice3(X1_53,X0_50))
% 15.56/2.47      | r2_hidden(k7_lattices(X0_50,sK2(X0_51,X1_53,X0_50)),X0_53)
% 15.56/2.47      | ~ v17_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v10_lattices(X0_50) ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_513,c_540]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_28321,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r1_lattices(sK4,X0_51,k7_lattices(X0_50,X1_51))
% 15.56/2.47      | ~ r2_hidden(X2_51,a_2_0_lattice3(X0_53,X0_50))
% 15.56/2.47      | ~ r2_hidden(X2_51,a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ m1_subset_1(k7_lattices(X0_50,sK2(X2_51,X0_53,X0_50)),u1_struct_0(sK4))
% 15.56/2.47      | ~ v17_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v10_lattices(X0_50)
% 15.56/2.47      | X0_51 != k7_lattices(sK4,sK5)
% 15.56/2.47      | sK2(X2_51,X0_53,X0_50) != X1_51 ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_27960,c_4670]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_30318,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r1_lattices(sK4,X0_51,k7_lattices(sK4,X1_51))
% 15.56/2.47      | ~ r2_hidden(X2_51,a_2_0_lattice3(X0_53,sK4))
% 15.56/2.47      | ~ r2_hidden(X2_51,a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ m1_subset_1(sK2(X2_51,X0_53,sK4),u1_struct_0(sK4))
% 15.56/2.47      | ~ v17_lattices(sK4)
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4)
% 15.56/2.47      | ~ v10_lattices(sK4)
% 15.56/2.47      | X0_51 != k7_lattices(sK4,sK5)
% 15.56/2.47      | sK2(X2_51,X0_53,sK4) != X1_51 ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_28321,c_528]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_46702,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r1_lattices(sK4,X0_51,k7_lattices(sK4,X1_51))
% 15.56/2.47      | ~ r2_hidden(X2_51,a_2_0_lattice3(X0_53,sK4))
% 15.56/2.47      | ~ r2_hidden(X2_51,a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ m1_subset_1(sK2(X2_51,X0_53,sK4),u1_struct_0(sK4))
% 15.56/2.47      | X0_51 != k7_lattices(sK4,sK5)
% 15.56/2.47      | sK2(X2_51,X0_53,sK4) != X1_51 ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_30318,c_27,c_26,c_25,c_24]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2,plain,
% 15.56/2.47      ( v6_lattices(X0)
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0)
% 15.56/2.47      | ~ v10_lattices(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f51]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_88,plain,
% 15.56/2.47      ( v6_lattices(sK4)
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4)
% 15.56/2.47      | ~ v10_lattices(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_2]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1,plain,
% 15.56/2.47      ( v8_lattices(X0)
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0)
% 15.56/2.47      | ~ v10_lattices(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f52]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_91,plain,
% 15.56/2.47      ( v8_lattices(sK4)
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4)
% 15.56/2.47      | ~ v10_lattices(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_1]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_0,plain,
% 15.56/2.47      ( ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0)
% 15.56/2.47      | ~ v10_lattices(X0)
% 15.56/2.47      | v9_lattices(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f53]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_94,plain,
% 15.56/2.47      ( ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4)
% 15.56/2.47      | ~ v10_lattices(sK4)
% 15.56/2.47      | v9_lattices(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_0]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_14,plain,
% 15.56/2.47      ( r4_lattice3(X0,X1,X2)
% 15.56/2.47      | r2_hidden(sK1(X0,X1,X2),X2)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f65]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_518,plain,
% 15.56/2.47      ( r4_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | r2_hidden(sK1(X0_50,X0_51,X0_53),X0_53)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_14]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_585,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 15.56/2.47      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_518]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_15,plain,
% 15.56/2.47      ( r4_lattice3(X0,X1,X2)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f64]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_517,plain,
% 15.56/2.47      ( r4_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | m1_subset_1(sK1(X0_50,X0_51,X0_53),u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_15]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_588,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4))
% 15.56/2.47      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_517]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_13,plain,
% 15.56/2.47      ( r4_lattice3(X0,X1,X2)
% 15.56/2.47      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f66]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_519,plain,
% 15.56/2.47      ( r4_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | ~ r1_lattices(X0_50,sK1(X0_50,X0_51,X0_53),X0_51)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_13]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_6,plain,
% 15.56/2.47      ( r1_lattices(X0,X1,X2)
% 15.56/2.47      | ~ r3_lattices(X0,X1,X2)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.56/2.47      | ~ v6_lattices(X0)
% 15.56/2.47      | ~ v8_lattices(X0)
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0)
% 15.56/2.47      | ~ v9_lattices(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f55]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_526,plain,
% 15.56/2.47      ( r1_lattices(X0_50,X0_51,X1_51)
% 15.56/2.47      | ~ r3_lattices(X0_50,X0_51,X1_51)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ v6_lattices(X0_50)
% 15.56/2.47      | ~ v8_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v9_lattices(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_6]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_10592,plain,
% 15.56/2.47      ( r4_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | ~ r3_lattices(X0_50,sK1(X0_50,X0_51,X0_53),X0_51)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ m1_subset_1(sK1(X0_50,X0_51,X0_53),u1_struct_0(X0_50))
% 15.56/2.47      | ~ v6_lattices(X0_50)
% 15.56/2.47      | ~ v8_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v9_lattices(X0_50) ),
% 15.56/2.47      inference(resolution,[status(thm)],[c_519,c_526]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_25471,plain,
% 15.56/2.47      ( ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ r3_lattices(X0_50,sK1(X0_50,X0_51,X0_53),X0_51)
% 15.56/2.47      | r4_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | ~ v6_lattices(X0_50)
% 15.56/2.47      | ~ v8_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v9_lattices(X0_50) ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_10592,c_517]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_25472,plain,
% 15.56/2.47      ( r4_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | ~ r3_lattices(X0_50,sK1(X0_50,X0_51,X0_53),X0_51)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ v6_lattices(X0_50)
% 15.56/2.47      | ~ v8_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v9_lattices(X0_50) ),
% 15.56/2.47      inference(renaming,[status(thm)],[c_25471]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_25474,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | ~ r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5)
% 15.56/2.47      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 15.56/2.47      | ~ v6_lattices(sK4)
% 15.56/2.47      | ~ v8_lattices(sK4)
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4)
% 15.56/2.47      | ~ v9_lattices(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_25472]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_509,negated_conjecture,
% 15.56/2.47      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_23]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1169,plain,
% 15.56/2.47      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1161,plain,
% 15.56/2.47      ( r4_lattice3(X0_50,X0_51,X0_53) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK1(X0_50,X0_51,X0_53),u1_struct_0(X0_50)) = iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_7,plain,
% 15.56/2.47      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.56/2.47      | ~ v17_lattices(X1)
% 15.56/2.47      | ~ l3_lattices(X1)
% 15.56/2.47      | v2_struct_0(X1)
% 15.56/2.47      | ~ v10_lattices(X1)
% 15.56/2.47      | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
% 15.56/2.47      inference(cnf_transformation,[],[f57]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_525,plain,
% 15.56/2.47      ( ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ v17_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v10_lattices(X0_50)
% 15.56/2.47      | k7_lattices(X0_50,k7_lattices(X0_50,X0_51)) = X0_51 ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_7]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1153,plain,
% 15.56/2.47      ( k7_lattices(X0_50,k7_lattices(X0_50,X0_51)) = X0_51
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2562,plain,
% 15.56/2.47      ( k7_lattices(X0_50,k7_lattices(X0_50,sK1(X0_50,X0_51,X0_53))) = sK1(X0_50,X0_51,X0_53)
% 15.56/2.47      | r4_lattice3(X0_50,X0_51,X0_53) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1161,c_1153]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_9953,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,X0_53))) = sK1(sK4,sK5,X0_53)
% 15.56/2.47      | r4_lattice3(sK4,sK5,X0_53) = iProver_top
% 15.56/2.47      | v17_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1169,c_2562]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_10046,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,X0_53))) = sK1(sK4,sK5,X0_53)
% 15.56/2.47      | r4_lattice3(sK4,sK5,X0_53) = iProver_top ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_9953,c_28,c_29,c_30,c_31]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_11,plain,
% 15.56/2.47      ( r3_lattice3(X0,X1,X2)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f60]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_521,plain,
% 15.56/2.47      ( r3_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | m1_subset_1(sK0(X0_50,X0_51,X0_53),u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_11]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1157,plain,
% 15.56/2.47      ( r3_lattice3(X0_50,X0_51,X0_53) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK0(X0_50,X0_51,X0_53),u1_struct_0(X0_50)) = iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2563,plain,
% 15.56/2.47      ( k7_lattices(X0_50,k7_lattices(X0_50,sK0(X0_50,X0_51,X0_53))) = sK0(X0_50,X0_51,X0_53)
% 15.56/2.47      | r3_lattice3(X0_50,X0_51,X0_53) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1157,c_1153]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_10434,plain,
% 15.56/2.47      ( k7_lattices(X0_50,k7_lattices(X0_50,sK0(X0_50,k7_lattices(X0_50,X0_51),X0_53))) = sK0(X0_50,k7_lattices(X0_50,X0_51),X0_53)
% 15.56/2.47      | r3_lattice3(X0_50,k7_lattices(X0_50,X0_51),X0_53) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1150,c_2563]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_21,negated_conjecture,
% 15.56/2.47      ( ~ r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | ~ r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.47      inference(cnf_transformation,[],[f77]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_511,negated_conjecture,
% 15.56/2.47      ( ~ r4_lattice3(sK4,sK5,sK3)
% 15.56/2.47      | ~ r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_21]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1167,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.47      | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_19484,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.47      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | v17_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_10434,c_1167]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_19867,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.47      | k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_19484,c_28,c_29,c_30,c_31,c_32]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_19868,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | r4_lattice3(sK4,sK5,sK3) != iProver_top ),
% 15.56/2.47      inference(renaming,[status(thm)],[c_19867]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_19874,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
% 15.56/2.47      | k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_10046,c_19868]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1152,plain,
% 15.56/2.47      ( r1_lattices(X0_50,X0_51,X1_51) = iProver_top
% 15.56/2.47      | r3_lattices(X0_50,X0_51,X1_51) != iProver_top
% 15.56/2.47      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v6_lattices(X0_50) != iProver_top
% 15.56/2.47      | v8_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v9_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_3832,plain,
% 15.56/2.47      ( r1_lattices(sK4,X0_51,sK5) = iProver_top
% 15.56/2.47      | r3_lattices(sK4,X0_51,sK5) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | v6_lattices(sK4) != iProver_top
% 15.56/2.47      | v8_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v9_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1169,c_1152]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_87,plain,
% 15.56/2.47      ( v6_lattices(X0) = iProver_top
% 15.56/2.47      | l3_lattices(X0) != iProver_top
% 15.56/2.47      | v2_struct_0(X0) = iProver_top
% 15.56/2.47      | v10_lattices(X0) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_89,plain,
% 15.56/2.47      ( v6_lattices(sK4) = iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_87]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_90,plain,
% 15.56/2.47      ( v8_lattices(X0) = iProver_top
% 15.56/2.47      | l3_lattices(X0) != iProver_top
% 15.56/2.47      | v2_struct_0(X0) = iProver_top
% 15.56/2.47      | v10_lattices(X0) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_92,plain,
% 15.56/2.47      ( v8_lattices(sK4) = iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_90]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_93,plain,
% 15.56/2.47      ( l3_lattices(X0) != iProver_top
% 15.56/2.47      | v2_struct_0(X0) = iProver_top
% 15.56/2.47      | v10_lattices(X0) != iProver_top
% 15.56/2.47      | v9_lattices(X0) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_95,plain,
% 15.56/2.47      ( l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top
% 15.56/2.47      | v9_lattices(sK4) = iProver_top ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_93]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_5388,plain,
% 15.56/2.47      ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | r3_lattices(sK4,X0_51,sK5) != iProver_top
% 15.56/2.47      | r1_lattices(sK4,X0_51,sK5) = iProver_top ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_3832,c_28,c_29,c_31,c_89,c_92,c_95]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_5389,plain,
% 15.56/2.47      ( r1_lattices(sK4,X0_51,sK5) = iProver_top
% 15.56/2.47      | r3_lattices(sK4,X0_51,sK5) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.47      inference(renaming,[status(thm)],[c_5388]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_5401,plain,
% 15.56/2.47      ( r1_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
% 15.56/2.47      | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1150,c_5389]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_5638,plain,
% 15.56/2.47      ( r1_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
% 15.56/2.47      | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_5401,c_28,c_31]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_20201,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
% 15.56/2.47      | r1_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))),sK5) = iProver_top
% 15.56/2.47      | r3_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK5) != iProver_top
% 15.56/2.47      | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_19874,c_5638]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_34,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.47      | r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_10,plain,
% 15.56/2.47      ( r3_lattice3(X0,X1,X2)
% 15.56/2.47      | r2_hidden(sK0(X0,X1,X2),X2)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f61]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_522,plain,
% 15.56/2.47      ( r3_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | r2_hidden(sK0(X0_50,X0_51,X0_53),X0_53)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_10]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1560,plain,
% 15.56/2.47      ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_522]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1561,plain,
% 15.56/2.47      ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) = iProver_top
% 15.56/2.47      | r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4)) = iProver_top
% 15.56/2.47      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_1560]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_20,plain,
% 15.56/2.47      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 15.56/2.47      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))
% 15.56/2.47      | ~ v17_lattices(X2)
% 15.56/2.47      | ~ l3_lattices(X2)
% 15.56/2.47      | v2_struct_0(X2)
% 15.56/2.47      | ~ v10_lattices(X2) ),
% 15.56/2.47      inference(cnf_transformation,[],[f67]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_512,plain,
% 15.56/2.47      ( ~ r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50))
% 15.56/2.47      | m1_subset_1(sK2(X0_51,X0_53,X0_50),u1_struct_0(X0_50))
% 15.56/2.47      | ~ v17_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v10_lattices(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_20]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1598,plain,
% 15.56/2.47      ( ~ r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4))
% 15.56/2.47      | ~ v17_lattices(sK4)
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4)
% 15.56/2.47      | ~ v10_lattices(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_512]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1599,plain,
% 15.56/2.47      ( r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) = iProver_top
% 15.56/2.47      | v17_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_1598]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_18,plain,
% 15.56/2.47      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 15.56/2.47      | r2_hidden(sK2(X0,X1,X2),X1)
% 15.56/2.47      | ~ v17_lattices(X2)
% 15.56/2.47      | ~ l3_lattices(X2)
% 15.56/2.47      | v2_struct_0(X2)
% 15.56/2.47      | ~ v10_lattices(X2) ),
% 15.56/2.47      inference(cnf_transformation,[],[f69]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_514,plain,
% 15.56/2.47      ( ~ r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50))
% 15.56/2.47      | r2_hidden(sK2(X0_51,X0_53,X0_50),X0_53)
% 15.56/2.47      | ~ v17_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v10_lattices(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_18]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1597,plain,
% 15.56/2.47      ( r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3)
% 15.56/2.47      | ~ r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ v17_lattices(sK4)
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4)
% 15.56/2.47      | ~ v10_lattices(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_514]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1601,plain,
% 15.56/2.47      ( r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) = iProver_top
% 15.56/2.47      | r2_hidden(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),a_2_0_lattice3(sK3,sK4)) != iProver_top
% 15.56/2.47      | v17_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_16,plain,
% 15.56/2.47      ( ~ r4_lattice3(X0,X1,X2)
% 15.56/2.47      | r1_lattices(X0,X3,X1)
% 15.56/2.47      | ~ r2_hidden(X3,X2)
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f63]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_516,plain,
% 15.56/2.47      ( ~ r4_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | r1_lattices(X0_50,X1_51,X0_51)
% 15.56/2.47      | ~ r2_hidden(X1_51,X0_53)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_16]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1800,plain,
% 15.56/2.47      ( ~ r4_lattice3(X0_50,X0_51,sK3)
% 15.56/2.47      | r1_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51)
% 15.56/2.47      | ~ r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_516]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1801,plain,
% 15.56/2.47      ( r4_lattice3(X0_50,X0_51,sK3) != iProver_top
% 15.56/2.47      | r1_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) = iProver_top
% 15.56/2.47      | r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1803,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.47      | r1_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) = iProver_top
% 15.56/2.47      | r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) != iProver_top
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_1801]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2155,plain,
% 15.56/2.47      ( ~ r1_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51)
% 15.56/2.47      | r3_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51)
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(X0_50))
% 15.56/2.47      | ~ v6_lattices(X0_50)
% 15.56/2.47      | ~ v8_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v9_lattices(X0_50) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_527]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2156,plain,
% 15.56/2.47      ( r1_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) != iProver_top
% 15.56/2.47      | r3_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v6_lattices(X0_50) != iProver_top
% 15.56/2.47      | v8_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v9_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_2155]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2158,plain,
% 15.56/2.47      ( r1_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) != iProver_top
% 15.56/2.47      | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) = iProver_top
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | v6_lattices(sK4) != iProver_top
% 15.56/2.47      | v8_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v9_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_2156]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_9,plain,
% 15.56/2.47      ( r3_lattice3(X0,X1,X2)
% 15.56/2.47      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f62]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_523,plain,
% 15.56/2.47      ( r3_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.47      | ~ r1_lattices(X0_50,X0_51,sK0(X0_50,X0_51,X0_53))
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_9]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2678,plain,
% 15.56/2.47      ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | ~ r1_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.47      | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
% 15.56/2.47      | ~ l3_lattices(sK4)
% 15.56/2.47      | v2_struct_0(sK4) ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_523]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2681,plain,
% 15.56/2.47      ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) = iProver_top
% 15.56/2.47      | r1_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != iProver_top
% 15.56/2.47      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_2678]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_10049,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
% 15.56/2.47      | r4_lattice3(sK4,sK5,sK3) = iProver_top ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_10046]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1156,plain,
% 15.56/2.47      ( r3_lattice3(X0_50,X0_51,X0_53) = iProver_top
% 15.56/2.47      | r2_hidden(sK0(X0_50,X0_51,X0_53),X0_53) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1165,plain,
% 15.56/2.47      ( k7_lattices(X0_50,sK2(X0_51,X0_53,X0_50)) = X0_51
% 15.56/2.47      | r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_2797,plain,
% 15.56/2.47      ( k7_lattices(X0_50,sK2(sK0(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)),X0_53,X0_50)) = sK0(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50))
% 15.56/2.47      | r3_lattice3(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X1_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X1_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X1_50) = iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_1156,c_1165]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_16137,plain,
% 15.56/2.47      ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.47      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | v17_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_2797,c_1167]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_17342,plain,
% 15.56/2.47      ( r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.47      | k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.47      inference(global_propositional_subsumption,
% 15.56/2.47                [status(thm)],
% 15.56/2.47                [c_16137,c_28,c_29,c_30,c_31,c_32,c_556]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_17343,plain,
% 15.56/2.47      ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | r4_lattice3(sK4,sK5,sK3) != iProver_top ),
% 15.56/2.47      inference(renaming,[status(thm)],[c_17342]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_17349,plain,
% 15.56/2.47      ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3) ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_10046,c_17343]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_8,plain,
% 15.56/2.47      ( ~ r3_lattices(X0,X1,X2)
% 15.56/2.47      | r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
% 15.56/2.47      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.56/2.47      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.56/2.47      | ~ v17_lattices(X0)
% 15.56/2.47      | ~ l3_lattices(X0)
% 15.56/2.47      | v2_struct_0(X0)
% 15.56/2.47      | ~ v10_lattices(X0) ),
% 15.56/2.47      inference(cnf_transformation,[],[f58]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_524,plain,
% 15.56/2.47      ( ~ r3_lattices(X0_50,X0_51,X1_51)
% 15.56/2.47      | r3_lattices(X0_50,k7_lattices(X0_50,X1_51),k7_lattices(X0_50,X0_51))
% 15.56/2.47      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 15.56/2.47      | ~ v17_lattices(X0_50)
% 15.56/2.47      | ~ l3_lattices(X0_50)
% 15.56/2.47      | v2_struct_0(X0_50)
% 15.56/2.47      | ~ v10_lattices(X0_50) ),
% 15.56/2.47      inference(subtyping,[status(esa)],[c_8]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1154,plain,
% 15.56/2.47      ( r3_lattices(X0_50,X0_51,X1_51) != iProver_top
% 15.56/2.47      | r3_lattices(X0_50,k7_lattices(X0_50,X1_51),k7_lattices(X0_50,X0_51)) = iProver_top
% 15.56/2.47      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.47      | v17_lattices(X0_50) != iProver_top
% 15.56/2.47      | l3_lattices(X0_50) != iProver_top
% 15.56/2.47      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.47      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.47      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_17560,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
% 15.56/2.47      | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) != iProver_top
% 15.56/2.47      | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
% 15.56/2.47      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | v17_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_17349,c_1154]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_17774,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
% 15.56/2.47      | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) != iProver_top
% 15.56/2.47      | r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | v17_lattices(sK4) != iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top
% 15.56/2.47      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.47      inference(instantiation,[status(thm)],[c_17560]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_17562,plain,
% 15.56/2.47      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
% 15.56/2.47      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
% 15.56/2.47      | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top
% 15.56/2.47      | l3_lattices(sK4) != iProver_top
% 15.56/2.47      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.47      inference(superposition,[status(thm)],[c_17349,c_1150]) ).
% 15.56/2.47  
% 15.56/2.47  cnf(c_1557,plain,
% 15.56/2.47      ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.47      | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4))
% 15.56/2.47      | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
% 15.56/2.48      | ~ l3_lattices(sK4)
% 15.56/2.48      | v2_struct_0(sK4) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_521]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1558,plain,
% 15.56/2.48      ( r3_lattice3(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) = iProver_top
% 15.56/2.48      | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_18490,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3)
% 15.56/2.48      | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_17562,c_28,c_31,c_32,c_34,c_556,c_1558,c_10049]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_8672,plain,
% 15.56/2.48      ( r1_lattices(X0_50,X0_51,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.48      | ~ r3_lattices(X0_50,X0_51,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.48      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.48      | ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(X0_50))
% 15.56/2.48      | ~ v6_lattices(X0_50)
% 15.56/2.48      | ~ v8_lattices(X0_50)
% 15.56/2.48      | ~ l3_lattices(X0_50)
% 15.56/2.48      | v2_struct_0(X0_50)
% 15.56/2.48      | ~ v9_lattices(X0_50) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_526]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_23001,plain,
% 15.56/2.48      ( r1_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.48      | ~ r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.48      | ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4))
% 15.56/2.48      | ~ m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4))
% 15.56/2.48      | ~ v6_lattices(sK4)
% 15.56/2.48      | ~ v8_lattices(sK4)
% 15.56/2.48      | ~ l3_lattices(sK4)
% 15.56/2.48      | v2_struct_0(sK4)
% 15.56/2.48      | ~ v9_lattices(sK4) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_8672]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_23002,plain,
% 15.56/2.48      ( r1_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != iProver_top
% 15.56/2.48      | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v6_lattices(sK4) != iProver_top
% 15.56/2.48      | v8_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v9_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_23001]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_27645,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = sK1(sK4,sK5,sK3) ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_20201,c_28,c_29,c_30,c_31,c_32,c_34,c_89,c_92,c_95,
% 15.56/2.48                 c_556,c_1561,c_1599,c_1601,c_1803,c_2158,c_2681,c_10049,
% 15.56/2.48                 c_17774,c_18490,c_23002]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2564,plain,
% 15.56/2.48      ( k7_lattices(X0_50,k7_lattices(X0_50,k7_lattices(X0_50,X0_51))) = k7_lattices(X0_50,X0_51)
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | v17_lattices(X0_50) != iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.48      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_1150,c_1153]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3749,plain,
% 15.56/2.48      ( k7_lattices(X0_50,k7_lattices(X0_50,k7_lattices(X0_50,sK1(X0_50,X0_51,X0_53)))) = k7_lattices(X0_50,sK1(X0_50,X0_51,X0_53))
% 15.56/2.48      | r4_lattice3(X0_50,X0_51,X0_53) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | v17_lattices(X0_50) != iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.48      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_1161,c_2564]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_13891,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,X0_53)))) = k7_lattices(sK4,sK1(sK4,sK5,X0_53))
% 15.56/2.48      | r4_lattice3(sK4,sK5,X0_53) = iProver_top
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_1169,c_3749]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_14292,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,X0_53)))) = k7_lattices(sK4,sK1(sK4,sK5,X0_53))
% 15.56/2.48      | r4_lattice3(sK4,sK5,X0_53) = iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_13891,c_28,c_29,c_30,c_31]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_19873,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.48      | k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3)) ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_14292,c_19868]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_20441,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
% 15.56/2.48      | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_19873,c_1150]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_14295,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
% 15.56/2.48      | r4_lattice3(sK4,sK5,sK3) = iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_14292]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_21129,plain,
% 15.56/2.48      ( m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top
% 15.56/2.48      | k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3)) ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_20441,c_28,c_31,c_32,c_34,c_556,c_1558,c_14295]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_21130,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
% 15.56/2.48      | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
% 15.56/2.48      inference(renaming,[status(thm)],[c_21129]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2466,plain,
% 15.56/2.48      ( r1_lattices(sK4,X0_51,sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,X0_51,sK5) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v6_lattices(sK4) != iProver_top
% 15.56/2.48      | v8_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v9_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_1169,c_1151]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3165,plain,
% 15.56/2.48      ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,X0_51,sK5) = iProver_top
% 15.56/2.48      | r1_lattices(sK4,X0_51,sK5) != iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_2466,c_28,c_29,c_31,c_89,c_92,c_95]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3166,plain,
% 15.56/2.48      ( r1_lattices(sK4,X0_51,sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,X0_51,sK5) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(renaming,[status(thm)],[c_3165]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_21155,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
% 15.56/2.48      | r1_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK5) = iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_21130,c_3166]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_17348,plain,
% 15.56/2.48      ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.48      | k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3)) ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_14292,c_17343]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_17806,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
% 15.56/2.48      | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),X0_51) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_17348,c_1154]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_18020,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3))
% 15.56/2.48      | r3_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
% 15.56/2.48      | m1_subset_1(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_17806]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_24357,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3)))) = k7_lattices(sK4,sK1(sK4,sK5,sK3)) ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_21155,c_28,c_29,c_30,c_31,c_32,c_34,c_89,c_92,c_95,
% 15.56/2.48                 c_556,c_1561,c_1599,c_1601,c_1803,c_2158,c_2681,c_14295,
% 15.56/2.48                 c_18020,c_21130,c_23002]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_24367,plain,
% 15.56/2.48      ( m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) = iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_24357,c_1150]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_24841,plain,
% 15.56/2.48      ( m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) = iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_24367,c_28,c_31]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_27652,plain,
% 15.56/2.48      ( m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) = iProver_top ),
% 15.56/2.48      inference(demodulation,[status(thm)],[c_27645,c_24841]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_27674,plain,
% 15.56/2.48      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4))
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) ),
% 15.56/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_27652]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_24370,plain,
% 15.56/2.48      ( r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,X0_51,k7_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))))) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v6_lattices(sK4) != iProver_top
% 15.56/2.48      | v8_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v9_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_24357,c_2469]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_24448,plain,
% 15.56/2.48      ( r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v6_lattices(sK4) != iProver_top
% 15.56/2.48      | v8_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v9_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(light_normalisation,[status(thm)],[c_24370,c_24357]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_38918,plain,
% 15.56/2.48      ( m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_24448,c_28,c_29,c_31,c_89,c_92,c_95]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_38919,plain,
% 15.56/2.48      ( r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(renaming,[status(thm)],[c_38918]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_38924,plain,
% 15.56/2.48      ( r1_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,X0_51,k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(light_normalisation,[status(thm)],[c_38919,c_27645]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_46561,plain,
% 15.56/2.48      ( r4_lattice3(sK4,sK5,sK3) = iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 15.56/2.48      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_46548,c_38924]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1695,plain,
% 15.56/2.48      ( ~ r4_lattice3(X0_50,X0_51,X0_53)
% 15.56/2.48      | r1_lattices(X0_50,sK1(X1_50,X1_51,X0_53),X0_51)
% 15.56/2.48      | ~ r2_hidden(sK1(X1_50,X1_51,X0_53),X0_53)
% 15.56/2.48      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.48      | ~ m1_subset_1(sK1(X1_50,X1_51,X0_53),u1_struct_0(X0_50))
% 15.56/2.48      | ~ l3_lattices(X0_50)
% 15.56/2.48      | v2_struct_0(X0_50) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_516]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1696,plain,
% 15.56/2.48      ( r4_lattice3(X0_50,X0_51,X0_53) != iProver_top
% 15.56/2.48      | r1_lattices(X0_50,sK1(X1_50,X1_51,X0_53),X0_51) = iProver_top
% 15.56/2.48      | r2_hidden(sK1(X1_50,X1_51,X0_53),X0_53) != iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK1(X1_50,X1_51,X0_53),u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_1695]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1698,plain,
% 15.56/2.48      ( r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.48      | r1_lattices(sK4,sK1(sK4,sK5,sK3),sK5) = iProver_top
% 15.56/2.48      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 15.56/2.48      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_1696]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3178,plain,
% 15.56/2.48      ( r1_lattices(sK4,k7_lattices(sK4,X0_51),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_1150,c_3166]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3402,plain,
% 15.56/2.48      ( r1_lattices(sK4,k7_lattices(sK4,X0_51),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_3178,c_28,c_31]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_27691,plain,
% 15.56/2.48      ( r1_lattices(sK4,sK1(sK4,sK5,sK3),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),sK5) = iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_27645,c_3402]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_27702,plain,
% 15.56/2.48      ( r1_lattices(sK4,sK1(sK4,sK5,sK3),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5) = iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(light_normalisation,[status(thm)],[c_27691,c_27645]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_24365,plain,
% 15.56/2.48      ( r3_lattices(sK4,k7_lattices(sK4,X0_51),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),X0_51) != iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_24357,c_1154]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_38541,plain,
% 15.56/2.48      ( r3_lattices(sK4,k7_lattices(sK4,X0_51),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),X0_51) != iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_24365,c_28,c_29,c_30,c_31]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_38547,plain,
% 15.56/2.48      ( r3_lattices(sK4,sK1(sK4,sK5,sK3),X0_51) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,X0_51),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(light_normalisation,[status(thm)],[c_38541,c_27645]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_38553,plain,
% 15.56/2.48      ( r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_38547]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47070,plain,
% 15.56/2.48      ( m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_46561,c_28,c_31,c_32,c_556,c_1698,c_27652,c_27702,
% 15.56/2.48                 c_38553]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47071,plain,
% 15.56/2.48      ( r3_lattices(sK4,k7_lattices(sK4,sK5),k7_lattices(sK4,sK1(sK4,sK5,sK3))) = iProver_top
% 15.56/2.48      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 15.56/2.48      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(renaming,[status(thm)],[c_47070]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2561,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK5)) = sK5
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_1169,c_1153]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_564,plain,
% 15.56/2.48      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 15.56/2.48      | ~ v17_lattices(sK4)
% 15.56/2.48      | ~ l3_lattices(sK4)
% 15.56/2.48      | v2_struct_0(sK4)
% 15.56/2.48      | ~ v10_lattices(sK4)
% 15.56/2.48      | k7_lattices(sK4,k7_lattices(sK4,sK5)) = sK5 ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_525]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3017,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK5)) = sK5 ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_2561,c_27,c_26,c_25,c_24,c_23,c_564]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_4536,plain,
% 15.56/2.48      ( r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),X0_51) != iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_3017,c_1154]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_9135,plain,
% 15.56/2.48      ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),X0_51) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_4536,c_28,c_29,c_30,c_31,c_32,c_556]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_9136,plain,
% 15.56/2.48      ( r3_lattices(sK4,k7_lattices(sK4,X0_51),sK5) = iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),X0_51) != iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(renaming,[status(thm)],[c_9135]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47078,plain,
% 15.56/2.48      ( r3_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK1(sK4,sK5,sK3))),sK5) = iProver_top
% 15.56/2.48      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 15.56/2.48      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_47071,c_9136]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47083,plain,
% 15.56/2.48      ( r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5) = iProver_top
% 15.56/2.48      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 15.56/2.48      | m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) != iProver_top ),
% 15.56/2.48      inference(light_normalisation,[status(thm)],[c_47078,c_27645]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47107,plain,
% 15.56/2.48      ( r3_lattices(sK4,sK1(sK4,sK5,sK3),sK5)
% 15.56/2.48      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 15.56/2.48      | ~ m1_subset_1(sK1(sK4,sK5,sK3),u1_struct_0(sK4))
% 15.56/2.48      | ~ m1_subset_1(k7_lattices(sK4,sK1(sK4,sK5,sK3)),u1_struct_0(sK4)) ),
% 15.56/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_47083]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47109,plain,
% 15.56/2.48      ( r4_lattice3(sK4,sK5,sK3) ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_46702,c_27,c_26,c_24,c_23,c_88,c_91,c_94,c_585,c_588,
% 15.56/2.48                 c_25474,c_27674,c_47107]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47111,plain,
% 15.56/2.48      ( r4_lattice3(sK4,sK5,sK3) = iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_47109]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47436,plain,
% 15.56/2.48      ( r4_lattice3(sK4,sK5,sK3) = iProver_top ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_46560,c_47111]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47443,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_47436,c_19868]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_47785,plain,
% 15.56/2.48      ( r3_lattices(sK4,k7_lattices(sK4,X0_51),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51) != iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_47443,c_1154]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_48090,plain,
% 15.56/2.48      ( r3_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK5),sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_47785]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1166,plain,
% 15.56/2.48      ( r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK2(X0_51,X0_53,X0_50),u1_struct_0(X0_50)) = iProver_top
% 15.56/2.48      | v17_lattices(X0_50) != iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.48      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2974,plain,
% 15.56/2.48      ( k7_lattices(X0_50,k7_lattices(X0_50,sK2(X0_51,X0_53,X0_50))) = sK2(X0_51,X0_53,X0_50)
% 15.56/2.48      | r2_hidden(X0_51,a_2_0_lattice3(X0_53,X0_50)) != iProver_top
% 15.56/2.48      | v17_lattices(X0_50) != iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.48      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_1166,c_1153]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_6213,plain,
% 15.56/2.48      ( k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)),X0_53,X0_50))) = sK2(sK0(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)),X0_53,X0_50)
% 15.56/2.48      | r3_lattice3(X1_50,X0_51,a_2_0_lattice3(X0_53,X0_50)) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(X1_50)) != iProver_top
% 15.56/2.48      | v17_lattices(X0_50) != iProver_top
% 15.56/2.48      | l3_lattices(X1_50) != iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X1_50) = iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.48      | v10_lattices(X0_50) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_1156,c_2974]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_41980,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)
% 15.56/2.48      | r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v17_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v10_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(superposition,[status(thm)],[c_6213,c_1167]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_43429,plain,
% 15.56/2.48      ( r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.48      | k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4) ),
% 15.56/2.48      inference(global_propositional_subsumption,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_41980,c_28,c_29,c_30,c_31,c_32,c_556]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_43430,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)
% 15.56/2.48      | r4_lattice3(sK4,sK5,sK3) != iProver_top ),
% 15.56/2.48      inference(renaming,[status(thm)],[c_43429]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_43431,plain,
% 15.56/2.48      ( ~ r4_lattice3(sK4,sK5,sK3)
% 15.56/2.48      | k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4) ),
% 15.56/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_43430]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_8829,plain,
% 15.56/2.48      ( r1_lattices(X0_50,X0_51,X1_51)
% 15.56/2.48      | ~ r1_lattices(X0_50,k7_lattices(sK4,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X2_51)
% 15.56/2.48      | X1_51 != X2_51
% 15.56/2.48      | X0_51 != k7_lattices(sK4,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_538]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_25082,plain,
% 15.56/2.48      ( r1_lattices(X0_50,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51)
% 15.56/2.48      | ~ r1_lattices(X0_50,k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X1_51)
% 15.56/2.48      | X0_51 != X1_51
% 15.56/2.48      | k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_8829]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_25083,plain,
% 15.56/2.48      ( X0_51 != X1_51
% 15.56/2.48      | k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)))
% 15.56/2.48      | r1_lattices(X0_50,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51) = iProver_top
% 15.56/2.48      | r1_lattices(X0_50,k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X1_51) != iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_25082]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_25085,plain,
% 15.56/2.48      ( k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)))
% 15.56/2.48      | sK5 != sK5
% 15.56/2.48      | r1_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),sK5) = iProver_top
% 15.56/2.48      | r1_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK5) != iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_25083]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_17344,plain,
% 15.56/2.48      ( ~ r4_lattice3(sK4,sK5,sK3)
% 15.56/2.48      | k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) = sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_17343]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2413,plain,
% 15.56/2.48      ( X0_51 != X1_51
% 15.56/2.48      | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != X1_51
% 15.56/2.48      | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = X0_51 ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_534]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_5564,plain,
% 15.56/2.48      ( X0_51 != k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.48      | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = X0_51
% 15.56/2.48      | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_2413]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_13044,plain,
% 15.56/2.48      ( k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.48      | k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = k7_lattices(X0_50,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)))
% 15.56/2.48      | k7_lattices(X0_50,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_5564]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_13045,plain,
% 15.56/2.48      ( k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) != k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.48      | k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)))
% 15.56/2.48      | k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_13044]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_8790,plain,
% 15.56/2.48      ( ~ m1_subset_1(k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4))
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(sK4))
% 15.56/2.48      | ~ l3_lattices(sK4)
% 15.56/2.48      | v2_struct_0(sK4) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_528]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_8793,plain,
% 15.56/2.48      ( m1_subset_1(k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(sK4)) = iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_8790]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_8795,plain,
% 15.56/2.48      ( m1_subset_1(k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(sK4)) = iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_8793]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_5367,plain,
% 15.56/2.48      ( ~ r1_lattices(X0_50,k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51)
% 15.56/2.48      | r3_lattices(X0_50,k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51)
% 15.56/2.48      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.48      | ~ m1_subset_1(k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(X0_50))
% 15.56/2.48      | ~ v6_lattices(X0_50)
% 15.56/2.48      | ~ v8_lattices(X0_50)
% 15.56/2.48      | ~ l3_lattices(X0_50)
% 15.56/2.48      | v2_struct_0(X0_50)
% 15.56/2.48      | ~ v9_lattices(X0_50) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_527]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_5368,plain,
% 15.56/2.48      ( r1_lattices(X0_50,k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51) != iProver_top
% 15.56/2.48      | r3_lattices(X0_50,k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),X0_51) = iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(X1_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | v6_lattices(X0_50) != iProver_top
% 15.56/2.48      | v8_lattices(X0_50) != iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top
% 15.56/2.48      | v9_lattices(X0_50) != iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_5367]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_5370,plain,
% 15.56/2.48      ( r1_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),sK5) != iProver_top
% 15.56/2.48      | r3_lattices(sK4,k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),sK5) = iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | v6_lattices(sK4) != iProver_top
% 15.56/2.48      | v8_lattices(sK4) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top
% 15.56/2.48      | v9_lattices(sK4) != iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_5368]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_536,plain,
% 15.56/2.48      ( ~ m1_subset_1(X0_51,X0_52)
% 15.56/2.48      | m1_subset_1(X1_51,X0_52)
% 15.56/2.48      | X1_51 != X0_51 ),
% 15.56/2.48      theory(equality) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1593,plain,
% 15.56/2.48      ( m1_subset_1(X0_51,u1_struct_0(sK4))
% 15.56/2.48      | ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4))
% 15.56/2.48      | X0_51 != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_536]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3627,plain,
% 15.56/2.48      ( ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4))
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4))
% 15.56/2.48      | k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_1593]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3633,plain,
% 15.56/2.48      ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.48      | m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_3627]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2040,plain,
% 15.56/2.48      ( X0_51 != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.48      | k7_lattices(X0_50,X0_51) = k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_535]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3084,plain,
% 15.56/2.48      ( k7_lattices(X0_50,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)))
% 15.56/2.48      | k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_2040]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_3085,plain,
% 15.56/2.48      ( k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)) != sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))
% 15.56/2.48      | k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) = k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_3084]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2956,plain,
% 15.56/2.48      ( ~ r4_lattice3(X0_50,X0_51,sK3)
% 15.56/2.48      | r1_lattices(X0_50,k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X0_51)
% 15.56/2.48      | ~ r2_hidden(k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3)
% 15.56/2.48      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 15.56/2.48      | ~ m1_subset_1(k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(X0_50))
% 15.56/2.48      | ~ l3_lattices(X0_50)
% 15.56/2.48      | v2_struct_0(X0_50) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_516]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2957,plain,
% 15.56/2.48      ( r4_lattice3(X0_50,X0_51,sK3) != iProver_top
% 15.56/2.48      | r1_lattices(X0_50,k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),X0_51) = iProver_top
% 15.56/2.48      | r2_hidden(k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3) != iProver_top
% 15.56/2.48      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(X1_50,k7_lattices(X1_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_2956]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2959,plain,
% 15.56/2.48      ( r4_lattice3(sK4,sK5,sK3) != iProver_top
% 15.56/2.48      | r1_lattices(sK4,k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK5) = iProver_top
% 15.56/2.48      | r2_hidden(k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_2957]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2410,plain,
% 15.56/2.48      ( k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_533]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2412,plain,
% 15.56/2.48      ( k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) = k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_2410]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2171,plain,
% 15.56/2.48      ( ~ m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(X0_50))
% 15.56/2.48      | m1_subset_1(k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(X0_50))
% 15.56/2.48      | ~ l3_lattices(X0_50)
% 15.56/2.48      | v2_struct_0(X0_50) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_528]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2172,plain,
% 15.56/2.48      ( m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(X0_50)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(X0_50,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(X0_50)) = iProver_top
% 15.56/2.48      | l3_lattices(X0_50) != iProver_top
% 15.56/2.48      | v2_struct_0(X0_50) = iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_2174,plain,
% 15.56/2.48      ( m1_subset_1(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),u1_struct_0(sK4)) != iProver_top
% 15.56/2.48      | m1_subset_1(k7_lattices(sK4,sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4))),u1_struct_0(sK4)) = iProver_top
% 15.56/2.48      | l3_lattices(sK4) != iProver_top
% 15.56/2.48      | v2_struct_0(sK4) = iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_2172]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1789,plain,
% 15.56/2.48      ( r2_hidden(X0_51,sK3)
% 15.56/2.48      | ~ r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3)
% 15.56/2.48      | X0_51 != sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_540]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1976,plain,
% 15.56/2.48      ( ~ r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3)
% 15.56/2.48      | r2_hidden(k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3)
% 15.56/2.48      | k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4) ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_1789]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1978,plain,
% 15.56/2.48      ( k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)
% 15.56/2.48      | r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) != iProver_top
% 15.56/2.48      | r2_hidden(k7_lattices(X0_50,k7_lattices(X0_50,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3) = iProver_top ),
% 15.56/2.48      inference(predicate_to_equality,[status(thm)],[c_1976]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_1980,plain,
% 15.56/2.48      ( k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))) != sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4)
% 15.56/2.48      | r2_hidden(sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4),sK3) != iProver_top
% 15.56/2.48      | r2_hidden(k7_lattices(sK4,k7_lattices(sK4,sK2(sK0(sK4,k7_lattices(sK4,sK5),a_2_0_lattice3(sK3,sK4)),sK3,sK4))),sK3) = iProver_top ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_1978]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(c_550,plain,
% 15.56/2.48      ( sK5 = sK5 ),
% 15.56/2.48      inference(instantiation,[status(thm)],[c_533]) ).
% 15.56/2.48  
% 15.56/2.48  cnf(contradiction,plain,
% 15.56/2.48      ( $false ),
% 15.56/2.48      inference(minisat,
% 15.56/2.48                [status(thm)],
% 15.56/2.48                [c_48090,c_47111,c_47109,c_43431,c_25085,c_23002,c_17344,
% 15.56/2.48                 c_13045,c_8795,c_5370,c_3633,c_3085,c_2959,c_2681,
% 15.56/2.48                 c_2412,c_2174,c_1980,c_1601,c_1561,c_1558,c_556,c_550,
% 15.56/2.48                 c_95,c_92,c_89,c_34,c_32,c_31,c_30,c_29,c_28]) ).
% 15.56/2.48  
% 15.56/2.48  
% 15.56/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.56/2.48  
% 15.56/2.48  ------                               Statistics
% 15.56/2.48  
% 15.56/2.48  ------ Selected
% 15.56/2.48  
% 15.56/2.48  total_time:                             1.666
% 15.56/2.48  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:19:07 EST 2020

% Result     : Theorem 11.93s
% Output     : CNFRefutation 11.93s
% Verified   : 
% Statistics : Number of formulae       :  220 (3503 expanded)
%              Number of clauses        :  167 ( 822 expanded)
%              Number of leaves         :   16 ( 803 expanded)
%              Depth                    :   27
%              Number of atoms          :  898 (24698 expanded)
%              Number of equality atoms :  223 ( 903 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & k7_lattices(X2,X4) = X0
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & k7_lattices(X2,sK1(X0,X1,X2)) = X0
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & k7_lattices(X2,sK1(X0,X1,X2)) = X0
            & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ r2_hidden(X3,X1)
      | k7_lattices(X2,X3) != X0
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k7_lattices(X2,X3),a_2_0_lattice3(X1,X2))
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r3_lattice3(X1,X2,X0)
          <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v17_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r3_lattice3(X1,X2,X0)
            <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r3_lattice3(X1,X2,X0) )
          & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r3_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r3_lattice3(X1,X2,X0) )
          & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r3_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r3_lattice3(X1,X2,X0) )
          & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r3_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ( ~ r4_lattice3(X1,k7_lattices(X1,sK4),a_2_0_lattice3(X0,X1))
          | ~ r3_lattice3(X1,sK4,X0) )
        & ( r4_lattice3(X1,k7_lattices(X1,sK4),a_2_0_lattice3(X0,X1))
          | r3_lattice3(X1,sK4,X0) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | ~ r3_lattice3(X1,X2,X0) )
            & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | r3_lattice3(X1,X2,X0) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r4_lattice3(sK3,k7_lattices(sK3,X2),a_2_0_lattice3(sK2,sK3))
            | ~ r3_lattice3(sK3,X2,sK2) )
          & ( r4_lattice3(sK3,k7_lattices(sK3,X2),a_2_0_lattice3(sK2,sK3))
            | r3_lattice3(sK3,X2,sK2) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v17_lattices(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
      | ~ r3_lattice3(sK3,sK4,sK2) )
    & ( r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
      | r3_lattice3(sK3,sK4,sK2) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v17_lattices(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f32,f31])).

fof(f48,plain,(
    v17_lattices(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X2,sK1(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r4_lattice3(X1,X2,X0)
              | ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
            & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | ~ r4_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,
    ( ~ r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
    | ~ r3_lattice3(sK3,sK4,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
      | ~ r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,
    ( r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
    | r3_lattice3(sK3,sK4,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k7_lattices(X2,X0),a_2_0_lattice3(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v17_lattices(X2)
    | v2_struct_0(X2)
    | ~ l3_lattices(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( v17_lattices(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_410,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k7_lattices(X2,X0),a_2_0_lattice3(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | v2_struct_0(X2)
    | ~ l3_lattices(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_411,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k7_lattices(sK3,X0),a_2_0_lattice3(X1,sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(k7_lattices(sK3,X0),a_2_0_lattice3(X1,sK3))
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_18,c_17,c_15])).

cnf(c_416,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k7_lattices(sK3,X0),a_2_0_lattice3(X1,sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_635,plain,
    ( ~ r2_hidden(X0_45,X0_48)
    | r2_hidden(k7_lattices(sK3,X0_45),a_2_0_lattice3(X0_48,sK3))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_983,plain,
    ( r2_hidden(X0_45,X0_48) != iProver_top
    | r2_hidden(k7_lattices(sK3,X0_45),a_2_0_lattice3(X0_48,sK3)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_642,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_976,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_4,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_467,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_468,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_472,plain,
    ( m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_18])).

cnf(c_473,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_633,plain,
    ( r3_lattice3(sK3,X0_45,X0_48)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_473])).

cnf(c_985,plain,
    ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ l3_lattices(sK3)
    | k7_lattices(sK3,k7_lattices(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k7_lattices(sK3,k7_lattices(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_18,c_17,c_15])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | k7_lattices(sK3,k7_lattices(sK3,X0_45)) = X0_45 ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_979,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,X0_45)) = X0_45
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_1524,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK0(sK3,X0_45,X0_48))) = sK0(sK3,X0_45,X0_48)
    | r3_lattice3(sK3,X0_45,X0_48) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_979])).

cnf(c_2635,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK0(sK3,sK4,X0_48))) = sK0(sK3,sK4,X0_48)
    | r3_lattice3(sK3,sK4,X0_48) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_1524])).

cnf(c_3,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_488,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_489,plain,
    ( r3_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_18])).

cnf(c_494,plain,
    ( r3_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_632,plain,
    ( r3_lattice3(sK3,X0_45,X0_48)
    | r2_hidden(sK0(sK3,X0_45,X0_48),X0_48)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_986,plain,
    ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
    | r2_hidden(sK0(sK3,X0_45,X0_48),X0_48) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ v10_lattices(X2)
    | ~ v17_lattices(X2)
    | v2_struct_0(X2)
    | ~ l3_lattices(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_392,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ v10_lattices(X2)
    | v2_struct_0(X2)
    | ~ l3_lattices(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_393,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
    | r2_hidden(sK1(X0,X1,sK3),X1)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( r2_hidden(sK1(X0,X1,sK3),X1)
    | ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_18,c_17,c_15])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
    | r2_hidden(sK1(X0,X1,sK3),X1) ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_636,plain,
    ( ~ r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3))
    | r2_hidden(sK1(X0_45,X0_48,sK3),X0_48) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_982,plain,
    ( r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3)) != iProver_top
    | r2_hidden(sK1(X0_45,X0_48,sK3),X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | ~ v10_lattices(X2)
    | ~ v17_lattices(X2)
    | v2_struct_0(X2)
    | ~ l3_lattices(X2)
    | k7_lattices(X2,sK1(X0,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | ~ v10_lattices(X2)
    | v2_struct_0(X2)
    | ~ l3_lattices(X2)
    | k7_lattices(X2,sK1(X0,X1,X2)) = X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ l3_lattices(sK3)
    | k7_lattices(sK3,sK1(X0,X1,sK3)) = X0 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_379,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
    | k7_lattices(sK3,sK1(X0,X1,sK3)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_18,c_17,c_15])).

cnf(c_637,plain,
    ( ~ r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3))
    | k7_lattices(sK3,sK1(X0_45,X0_48,sK3)) = X0_45 ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_981,plain,
    ( k7_lattices(sK3,sK1(X0_45,X0_48,sK3)) = X0_45
    | r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_1185,plain,
    ( k7_lattices(sK3,sK1(sK1(X0_45,a_2_0_lattice3(X0_48,sK3),sK3),X0_48,sK3)) = sK1(X0_45,a_2_0_lattice3(X0_48,sK3),sK3)
    | r2_hidden(X0_45,a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_981])).

cnf(c_1851,plain,
    ( k7_lattices(sK3,sK1(sK1(sK0(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)),a_2_0_lattice3(X0_48,sK3),sK3),X0_48,sK3)) = sK1(sK0(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)),a_2_0_lattice3(X0_48,sK3),sK3)
    | r3_lattice3(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_1185])).

cnf(c_10,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r3_lattice3(X0,k7_lattices(X0,X1),a_2_0_lattice3(X2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v17_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,negated_conjecture,
    ( ~ r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
    | ~ r3_lattice3(sK3,sK4,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_140,plain,
    ( ~ r3_lattice3(sK3,sK4,sK2)
    | ~ r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_141,plain,
    ( ~ r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
    | ~ r3_lattice3(sK3,sK4,sK2) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_296,plain,
    ( ~ r3_lattice3(X0,k7_lattices(X0,X1),a_2_0_lattice3(X2,X0))
    | ~ r3_lattice3(sK3,sK4,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v17_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | a_2_0_lattice3(sK2,sK3) != X2
    | k7_lattices(sK3,sK4) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_141])).

cnf(c_297,plain,
    ( ~ r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | ~ r3_lattice3(sK3,sK4,sK2)
    | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3))
    | ~ v10_lattices(sK3)
    | ~ v17_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_299,plain,
    ( ~ r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | ~ r3_lattice3(sK3,sK4,sK2)
    | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_297,c_18,c_17,c_16,c_15])).

cnf(c_641,plain,
    ( ~ r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | ~ r3_lattice3(sK3,sK4,sK2)
    | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_299])).

cnf(c_977,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
    | r3_lattice3(sK3,sK4,sK2) != iProver_top
    | m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_301,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
    | r3_lattice3(sK3,sK4,sK2) != iProver_top
    | m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k7_lattices(sK3,X0),u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_514,plain,
    ( m1_subset_1(k7_lattices(sK3,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_18])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k7_lattices(sK3,X0),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_514])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | m1_subset_1(k7_lattices(sK3,X0_45),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_515])).

cnf(c_681,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_lattices(sK3,X0_45),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_683,plain,
    ( m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_1273,plain,
    ( r3_lattice3(sK3,sK4,sK2) != iProver_top
    | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_977,c_23,c_301,c_683])).

cnf(c_1274,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
    | r3_lattice3(sK3,sK4,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1273])).

cnf(c_1080,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_976,c_979])).

cnf(c_1277,plain,
    ( r3_lattice3(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
    | r3_lattice3(sK3,sK4,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1274,c_1080])).

cnf(c_12420,plain,
    ( k7_lattices(sK3,sK1(sK1(sK0(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)) = sK1(sK0(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)
    | r3_lattice3(sK3,sK4,sK2) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1851,c_1277])).

cnf(c_660,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k7_lattices(sK3,k7_lattices(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_2,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_262,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X3,X4,X5)
    | ~ r2_hidden(X6,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X6,u1_struct_0(X0))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | X0 != X3
    | X1 != X4
    | sK0(X3,X4,X5) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_263,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(sK0(X0,X1,X3),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X0,X1,X3),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_279,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(sK0(X0,X1,X3),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_263,c_4])).

cnf(c_447,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(sK0(X0,X1,X3),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_279,c_15])).

cnf(c_448,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattice3(sK3,X0,X2)
    | ~ r2_hidden(sK0(sK3,X0,X2),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK3,X0,X2),X1)
    | r3_lattice3(sK3,X0,X2)
    | ~ r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_18])).

cnf(c_451,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattice3(sK3,X0,X2)
    | ~ r2_hidden(sK0(sK3,X0,X2),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_450])).

cnf(c_634,plain,
    ( ~ r3_lattice3(sK3,X0_45,X0_48)
    | r3_lattice3(sK3,X0_45,X1_48)
    | ~ r2_hidden(sK0(sK3,X0_45,X1_48),X0_48)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_1081,plain,
    ( ~ r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),X0_48)
    | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | ~ r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),X0_48)
    | ~ m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_1082,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),X0_48) != iProver_top
    | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),X0_48) != iProver_top
    | m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_1084,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),sK2) != iProver_top
    | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),sK2) != iProver_top
    | m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_1086,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | ~ m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1090,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_1128,plain,
    ( r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3))
    | ~ r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1132,plain,
    ( r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) = iProver_top
    | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_1127,plain,
    ( ~ r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) = sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1134,plain,
    ( k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) = sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0_45,X0_46)
    | m1_subset_1(X1_45,X0_46)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_1092,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | X0_45 != sK4 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_1137,plain,
    ( m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k7_lattices(sK3,k7_lattices(sK3,sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_1092])).

cnf(c_1138,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK4)) != sK4
    | m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_644,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1384,plain,
    ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v17_lattices(X2)
    | v2_struct_0(X2)
    | ~ l3_lattices(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | v2_struct_0(X2)
    | ~ l3_lattices(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
    | m1_subset_1(sK1(X0,X1,sK3),u1_struct_0(sK3))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_361,plain,
    ( m1_subset_1(sK1(X0,X1,sK3),u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_18,c_17,c_15])).

cnf(c_362,plain,
    ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
    | m1_subset_1(sK1(X0,X1,sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_638,plain,
    ( ~ r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3))
    | m1_subset_1(sK1(X0_45,X0_48,sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_1631,plain,
    ( ~ r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3))
    | m1_subset_1(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1632,plain,
    ( r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) != iProver_top
    | m1_subset_1(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1631])).

cnf(c_1630,plain,
    ( r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2)
    | ~ r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1634,plain,
    ( r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2) = iProver_top
    | r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1630])).

cnf(c_1629,plain,
    ( ~ r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3))
    | k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)) = sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1636,plain,
    ( k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)) = sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)
    | r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1629])).

cnf(c_648,plain,
    ( ~ r3_lattice3(X0_47,X0_45,X0_48)
    | r3_lattice3(X0_47,X1_45,X0_48)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_1709,plain,
    ( ~ r3_lattice3(sK3,X0_45,X0_48)
    | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),X0_48)
    | k7_lattices(sK3,k7_lattices(sK3,sK4)) != X0_45 ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_1710,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK4)) != X0_45
    | r3_lattice3(sK3,X0_45,X0_48) != iProver_top
    | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1709])).

cnf(c_1712,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK4)) != sK4
    | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),sK2) = iProver_top
    | r3_lattice3(sK3,sK4,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1710])).

cnf(c_649,plain,
    ( ~ r2_hidden(X0_45,X0_48)
    | r2_hidden(X1_45,X0_48)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_2004,plain,
    ( r2_hidden(X0_45,sK2)
    | ~ r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2)
    | X0_45 != sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_3154,plain,
    ( ~ r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2)
    | r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2)
    | k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) != sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_3156,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) != sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)
    | r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2) != iProver_top
    | r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3154])).

cnf(c_3155,plain,
    ( ~ m1_subset_1(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),u1_struct_0(sK3))
    | k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) = sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_3158,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) = sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)
    | m1_subset_1(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3155])).

cnf(c_645,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1224,plain,
    ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != X0_45
    | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,X1_45)
    | k7_lattices(sK3,X1_45) != X0_45 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1841,plain,
    ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,X0_45)
    | k7_lattices(sK3,X0_45) != sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_3561,plain,
    ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3))
    | k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) != sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_1841])).

cnf(c_646,plain,
    ( X0_45 != X1_45
    | k7_lattices(X0_47,X0_45) = k7_lattices(X0_47,X1_45) ),
    theory(equality)).

cnf(c_2513,plain,
    ( X0_45 != X1_45
    | k7_lattices(sK3,X0_45) = k7_lattices(sK3,X1_45) ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_3594,plain,
    ( X0_45 != sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)
    | k7_lattices(sK3,X0_45) = k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_6764,plain,
    ( k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)) != sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)
    | k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) = k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_3594])).

cnf(c_5256,plain,
    ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,X0_45)
    | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3))
    | k7_lattices(sK3,X0_45) != k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_13641,plain,
    ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3))
    | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)))
    | k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) != k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_5256])).

cnf(c_3932,plain,
    ( r2_hidden(X0_45,sK2)
    | ~ r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2)
    | X0_45 != k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_34130,plain,
    ( r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),sK2)
    | ~ r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2)
    | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_3932])).

cnf(c_34131,plain,
    ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)))
    | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),sK2) = iProver_top
    | r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34130])).

cnf(c_36474,plain,
    ( r3_lattice3(sK3,sK4,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12420,c_14,c_23,c_301,c_660,c_683,c_1084,c_1090,c_1132,c_1134,c_1138,c_1384,c_1632,c_1634,c_1636,c_1712,c_3156,c_3158,c_3561,c_6764,c_13641,c_34131])).

cnf(c_36483,plain,
    ( k7_lattices(sK3,k7_lattices(sK3,sK0(sK3,sK4,sK2))) = sK0(sK3,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_2635,c_36474])).

cnf(c_36545,plain,
    ( r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(X0_48,sK3)) = iProver_top
    | r2_hidden(k7_lattices(sK3,sK0(sK3,sK4,sK2)),X0_48) != iProver_top
    | m1_subset_1(k7_lattices(sK3,sK0(sK3,sK4,sK2)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36483,c_983])).

cnf(c_675,plain,
    ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_677,plain,
    ( r3_lattice3(sK3,sK4,sK2) = iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1431,plain,
    ( ~ m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3))
    | m1_subset_1(k7_lattices(sK3,sK0(sK3,X0_45,X0_48)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1432,plain,
    ( m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_lattices(sK3,sK0(sK3,X0_45,X0_48)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1431])).

cnf(c_1434,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_lattices(sK3,sK0(sK3,sK4,sK2)),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_37389,plain,
    ( r2_hidden(k7_lattices(sK3,sK0(sK3,sK4,sK2)),X0_48) != iProver_top
    | r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(X0_48,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36545,c_14,c_23,c_301,c_660,c_677,c_683,c_1084,c_1090,c_1132,c_1134,c_1138,c_1384,c_1434,c_1632,c_1634,c_1636,c_1712,c_3156,c_3158,c_3561,c_6764,c_13641,c_34131])).

cnf(c_37390,plain,
    ( r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(X0_48,sK3)) = iProver_top
    | r2_hidden(k7_lattices(sK3,sK0(sK3,sK4,sK2)),X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_37389])).

cnf(c_37397,plain,
    ( r2_hidden(sK0(sK3,sK4,sK2),X0_48) != iProver_top
    | r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)) = iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_983,c_37390])).

cnf(c_37399,plain,
    ( r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | r2_hidden(sK0(sK3,sK4,sK2),sK2) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37397])).

cnf(c_11,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r3_lattice3(X0,k7_lattices(X0,X1),a_2_0_lattice3(X2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v17_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
    | r3_lattice3(sK3,sK4,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_142,plain,
    ( r3_lattice3(sK3,sK4,sK2)
    | r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_143,plain,
    ( r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
    | r3_lattice3(sK3,sK4,sK2) ),
    inference(renaming,[status(thm)],[c_142])).

cnf(c_313,plain,
    ( r3_lattice3(X0,k7_lattices(X0,X1),a_2_0_lattice3(X2,X0))
    | r3_lattice3(sK3,sK4,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v17_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | a_2_0_lattice3(sK2,sK3) != X2
    | k7_lattices(sK3,sK4) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_143])).

cnf(c_314,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | r3_lattice3(sK3,sK4,sK2)
    | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3))
    | ~ v10_lattices(sK3)
    | ~ v17_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_316,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | r3_lattice3(sK3,sK4,sK2)
    | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_18,c_17,c_16,c_15])).

cnf(c_640,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | r3_lattice3(sK3,sK4,sK2)
    | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_316])).

cnf(c_978,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | r3_lattice3(sK3,sK4,sK2) = iProver_top
    | m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_318,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | r3_lattice3(sK3,sK4,sK2) = iProver_top
    | m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1349,plain,
    ( r3_lattice3(sK3,sK4,sK2) = iProver_top
    | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_978,c_23,c_318,c_683])).

cnf(c_1350,plain,
    ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | r3_lattice3(sK3,sK4,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_1349])).

cnf(c_1353,plain,
    ( r3_lattice3(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
    | r3_lattice3(sK3,sK4,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1350,c_1080])).

cnf(c_1264,plain,
    ( r3_lattice3(sK3,X0_45,X0_48)
    | ~ r3_lattice3(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | ~ r2_hidden(sK0(sK3,X0_45,X0_48),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_1265,plain,
    ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
    | r3_lattice3(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
    | r2_hidden(sK0(sK3,X0_45,X0_48),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_1267,plain,
    ( r3_lattice3(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
    | r3_lattice3(sK3,sK4,sK2) = iProver_top
    | r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_678,plain,
    ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
    | r2_hidden(sK0(sK3,X0_45,X0_48),X0_48) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_680,plain,
    ( r3_lattice3(sK3,sK4,sK2) = iProver_top
    | r2_hidden(sK0(sK3,sK4,sK2),sK2) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37399,c_36474,c_1353,c_1267,c_680,c_677,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:29:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.93/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.93/1.99  
% 11.93/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.93/1.99  
% 11.93/1.99  ------  iProver source info
% 11.93/1.99  
% 11.93/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.93/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.93/1.99  git: non_committed_changes: false
% 11.93/1.99  git: last_make_outside_of_git: false
% 11.93/1.99  
% 11.93/1.99  ------ 
% 11.93/1.99  
% 11.93/1.99  ------ Input Options
% 11.93/1.99  
% 11.93/1.99  --out_options                           all
% 11.93/1.99  --tptp_safe_out                         true
% 11.93/1.99  --problem_path                          ""
% 11.93/1.99  --include_path                          ""
% 11.93/1.99  --clausifier                            res/vclausify_rel
% 11.93/1.99  --clausifier_options                    --mode clausify
% 11.93/1.99  --stdin                                 false
% 11.93/1.99  --stats_out                             all
% 11.93/1.99  
% 11.93/1.99  ------ General Options
% 11.93/1.99  
% 11.93/1.99  --fof                                   false
% 11.93/1.99  --time_out_real                         305.
% 11.93/1.99  --time_out_virtual                      -1.
% 11.93/1.99  --symbol_type_check                     false
% 11.93/1.99  --clausify_out                          false
% 11.93/1.99  --sig_cnt_out                           false
% 11.93/1.99  --trig_cnt_out                          false
% 11.93/1.99  --trig_cnt_out_tolerance                1.
% 11.93/1.99  --trig_cnt_out_sk_spl                   false
% 11.93/1.99  --abstr_cl_out                          false
% 11.93/1.99  
% 11.93/1.99  ------ Global Options
% 11.93/1.99  
% 11.93/1.99  --schedule                              default
% 11.93/1.99  --add_important_lit                     false
% 11.93/1.99  --prop_solver_per_cl                    1000
% 11.93/1.99  --min_unsat_core                        false
% 11.93/1.99  --soft_assumptions                      false
% 11.93/1.99  --soft_lemma_size                       3
% 11.93/1.99  --prop_impl_unit_size                   0
% 11.93/1.99  --prop_impl_unit                        []
% 11.93/1.99  --share_sel_clauses                     true
% 11.93/1.99  --reset_solvers                         false
% 11.93/1.99  --bc_imp_inh                            [conj_cone]
% 11.93/1.99  --conj_cone_tolerance                   3.
% 11.93/1.99  --extra_neg_conj                        none
% 11.93/1.99  --large_theory_mode                     true
% 11.93/1.99  --prolific_symb_bound                   200
% 11.93/1.99  --lt_threshold                          2000
% 11.93/1.99  --clause_weak_htbl                      true
% 11.93/1.99  --gc_record_bc_elim                     false
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing Options
% 11.93/2.00  
% 11.93/2.00  --preprocessing_flag                    true
% 11.93/2.00  --time_out_prep_mult                    0.1
% 11.93/2.00  --splitting_mode                        input
% 11.93/2.00  --splitting_grd                         true
% 11.93/2.00  --splitting_cvd                         false
% 11.93/2.00  --splitting_cvd_svl                     false
% 11.93/2.00  --splitting_nvd                         32
% 11.93/2.00  --sub_typing                            true
% 11.93/2.00  --prep_gs_sim                           true
% 11.93/2.00  --prep_unflatten                        true
% 11.93/2.00  --prep_res_sim                          true
% 11.93/2.00  --prep_upred                            true
% 11.93/2.00  --prep_sem_filter                       exhaustive
% 11.93/2.00  --prep_sem_filter_out                   false
% 11.93/2.00  --pred_elim                             true
% 11.93/2.00  --res_sim_input                         true
% 11.93/2.00  --eq_ax_congr_red                       true
% 11.93/2.00  --pure_diseq_elim                       true
% 11.93/2.00  --brand_transform                       false
% 11.93/2.00  --non_eq_to_eq                          false
% 11.93/2.00  --prep_def_merge                        true
% 11.93/2.00  --prep_def_merge_prop_impl              false
% 11.93/2.00  --prep_def_merge_mbd                    true
% 11.93/2.00  --prep_def_merge_tr_red                 false
% 11.93/2.00  --prep_def_merge_tr_cl                  false
% 11.93/2.00  --smt_preprocessing                     true
% 11.93/2.00  --smt_ac_axioms                         fast
% 11.93/2.00  --preprocessed_out                      false
% 11.93/2.00  --preprocessed_stats                    false
% 11.93/2.00  
% 11.93/2.00  ------ Abstraction refinement Options
% 11.93/2.00  
% 11.93/2.00  --abstr_ref                             []
% 11.93/2.00  --abstr_ref_prep                        false
% 11.93/2.00  --abstr_ref_until_sat                   false
% 11.93/2.00  --abstr_ref_sig_restrict                funpre
% 11.93/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.93/2.00  --abstr_ref_under                       []
% 11.93/2.00  
% 11.93/2.00  ------ SAT Options
% 11.93/2.00  
% 11.93/2.00  --sat_mode                              false
% 11.93/2.00  --sat_fm_restart_options                ""
% 11.93/2.00  --sat_gr_def                            false
% 11.93/2.00  --sat_epr_types                         true
% 11.93/2.00  --sat_non_cyclic_types                  false
% 11.93/2.00  --sat_finite_models                     false
% 11.93/2.00  --sat_fm_lemmas                         false
% 11.93/2.00  --sat_fm_prep                           false
% 11.93/2.00  --sat_fm_uc_incr                        true
% 11.93/2.00  --sat_out_model                         small
% 11.93/2.00  --sat_out_clauses                       false
% 11.93/2.00  
% 11.93/2.00  ------ QBF Options
% 11.93/2.00  
% 11.93/2.00  --qbf_mode                              false
% 11.93/2.00  --qbf_elim_univ                         false
% 11.93/2.00  --qbf_dom_inst                          none
% 11.93/2.00  --qbf_dom_pre_inst                      false
% 11.93/2.00  --qbf_sk_in                             false
% 11.93/2.00  --qbf_pred_elim                         true
% 11.93/2.00  --qbf_split                             512
% 11.93/2.00  
% 11.93/2.00  ------ BMC1 Options
% 11.93/2.00  
% 11.93/2.00  --bmc1_incremental                      false
% 11.93/2.00  --bmc1_axioms                           reachable_all
% 11.93/2.00  --bmc1_min_bound                        0
% 11.93/2.00  --bmc1_max_bound                        -1
% 11.93/2.00  --bmc1_max_bound_default                -1
% 11.93/2.00  --bmc1_symbol_reachability              true
% 11.93/2.00  --bmc1_property_lemmas                  false
% 11.93/2.00  --bmc1_k_induction                      false
% 11.93/2.00  --bmc1_non_equiv_states                 false
% 11.93/2.00  --bmc1_deadlock                         false
% 11.93/2.00  --bmc1_ucm                              false
% 11.93/2.00  --bmc1_add_unsat_core                   none
% 11.93/2.00  --bmc1_unsat_core_children              false
% 11.93/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.93/2.00  --bmc1_out_stat                         full
% 11.93/2.00  --bmc1_ground_init                      false
% 11.93/2.00  --bmc1_pre_inst_next_state              false
% 11.93/2.00  --bmc1_pre_inst_state                   false
% 11.93/2.00  --bmc1_pre_inst_reach_state             false
% 11.93/2.00  --bmc1_out_unsat_core                   false
% 11.93/2.00  --bmc1_aig_witness_out                  false
% 11.93/2.00  --bmc1_verbose                          false
% 11.93/2.00  --bmc1_dump_clauses_tptp                false
% 11.93/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.93/2.00  --bmc1_dump_file                        -
% 11.93/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.93/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.93/2.00  --bmc1_ucm_extend_mode                  1
% 11.93/2.00  --bmc1_ucm_init_mode                    2
% 11.93/2.00  --bmc1_ucm_cone_mode                    none
% 11.93/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.93/2.00  --bmc1_ucm_relax_model                  4
% 11.93/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.93/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.93/2.00  --bmc1_ucm_layered_model                none
% 11.93/2.00  --bmc1_ucm_max_lemma_size               10
% 11.93/2.00  
% 11.93/2.00  ------ AIG Options
% 11.93/2.00  
% 11.93/2.00  --aig_mode                              false
% 11.93/2.00  
% 11.93/2.00  ------ Instantiation Options
% 11.93/2.00  
% 11.93/2.00  --instantiation_flag                    true
% 11.93/2.00  --inst_sos_flag                         false
% 11.93/2.00  --inst_sos_phase                        true
% 11.93/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.93/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.93/2.00  --inst_lit_sel_side                     num_symb
% 11.93/2.00  --inst_solver_per_active                1400
% 11.93/2.00  --inst_solver_calls_frac                1.
% 11.93/2.00  --inst_passive_queue_type               priority_queues
% 11.93/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.93/2.00  --inst_passive_queues_freq              [25;2]
% 11.93/2.00  --inst_dismatching                      true
% 11.93/2.00  --inst_eager_unprocessed_to_passive     true
% 11.93/2.00  --inst_prop_sim_given                   true
% 11.93/2.00  --inst_prop_sim_new                     false
% 11.93/2.00  --inst_subs_new                         false
% 11.93/2.00  --inst_eq_res_simp                      false
% 11.93/2.00  --inst_subs_given                       false
% 11.93/2.00  --inst_orphan_elimination               true
% 11.93/2.00  --inst_learning_loop_flag               true
% 11.93/2.00  --inst_learning_start                   3000
% 11.93/2.00  --inst_learning_factor                  2
% 11.93/2.00  --inst_start_prop_sim_after_learn       3
% 11.93/2.00  --inst_sel_renew                        solver
% 11.93/2.00  --inst_lit_activity_flag                true
% 11.93/2.00  --inst_restr_to_given                   false
% 11.93/2.00  --inst_activity_threshold               500
% 11.93/2.00  --inst_out_proof                        true
% 11.93/2.00  
% 11.93/2.00  ------ Resolution Options
% 11.93/2.00  
% 11.93/2.00  --resolution_flag                       true
% 11.93/2.00  --res_lit_sel                           adaptive
% 11.93/2.00  --res_lit_sel_side                      none
% 11.93/2.00  --res_ordering                          kbo
% 11.93/2.00  --res_to_prop_solver                    active
% 11.93/2.00  --res_prop_simpl_new                    false
% 11.93/2.00  --res_prop_simpl_given                  true
% 11.93/2.00  --res_passive_queue_type                priority_queues
% 11.93/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.93/2.00  --res_passive_queues_freq               [15;5]
% 11.93/2.00  --res_forward_subs                      full
% 11.93/2.00  --res_backward_subs                     full
% 11.93/2.00  --res_forward_subs_resolution           true
% 11.93/2.00  --res_backward_subs_resolution          true
% 11.93/2.00  --res_orphan_elimination                true
% 11.93/2.00  --res_time_limit                        2.
% 11.93/2.00  --res_out_proof                         true
% 11.93/2.00  
% 11.93/2.00  ------ Superposition Options
% 11.93/2.00  
% 11.93/2.00  --superposition_flag                    true
% 11.93/2.00  --sup_passive_queue_type                priority_queues
% 11.93/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.93/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.93/2.00  --demod_completeness_check              fast
% 11.93/2.00  --demod_use_ground                      true
% 11.93/2.00  --sup_to_prop_solver                    passive
% 11.93/2.00  --sup_prop_simpl_new                    true
% 11.93/2.00  --sup_prop_simpl_given                  true
% 11.93/2.00  --sup_fun_splitting                     false
% 11.93/2.00  --sup_smt_interval                      50000
% 11.93/2.00  
% 11.93/2.00  ------ Superposition Simplification Setup
% 11.93/2.00  
% 11.93/2.00  --sup_indices_passive                   []
% 11.93/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.93/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_full_bw                           [BwDemod]
% 11.93/2.00  --sup_immed_triv                        [TrivRules]
% 11.93/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.93/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_immed_bw_main                     []
% 11.93/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.93/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.93/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.93/2.00  
% 11.93/2.00  ------ Combination Options
% 11.93/2.00  
% 11.93/2.00  --comb_res_mult                         3
% 11.93/2.00  --comb_sup_mult                         2
% 11.93/2.00  --comb_inst_mult                        10
% 11.93/2.00  
% 11.93/2.00  ------ Debug Options
% 11.93/2.00  
% 11.93/2.00  --dbg_backtrace                         false
% 11.93/2.00  --dbg_dump_prop_clauses                 false
% 11.93/2.00  --dbg_dump_prop_clauses_file            -
% 11.93/2.00  --dbg_out_stat                          false
% 11.93/2.00  ------ Parsing...
% 11.93/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.93/2.00  ------ Proving...
% 11.93/2.00  ------ Problem Properties 
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  clauses                                 12
% 11.93/2.00  conjectures                             1
% 11.93/2.00  EPR                                     0
% 11.93/2.00  Horn                                    9
% 11.93/2.00  unary                                   1
% 11.93/2.00  binary                                  5
% 11.93/2.00  lits                                    30
% 11.93/2.00  lits eq                                 2
% 11.93/2.00  fd_pure                                 0
% 11.93/2.00  fd_pseudo                               0
% 11.93/2.00  fd_cond                                 0
% 11.93/2.00  fd_pseudo_cond                          0
% 11.93/2.00  AC symbols                              0
% 11.93/2.00  
% 11.93/2.00  ------ Schedule dynamic 5 is on 
% 11.93/2.00  
% 11.93/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ 
% 11.93/2.00  Current options:
% 11.93/2.00  ------ 
% 11.93/2.00  
% 11.93/2.00  ------ Input Options
% 11.93/2.00  
% 11.93/2.00  --out_options                           all
% 11.93/2.00  --tptp_safe_out                         true
% 11.93/2.00  --problem_path                          ""
% 11.93/2.00  --include_path                          ""
% 11.93/2.00  --clausifier                            res/vclausify_rel
% 11.93/2.00  --clausifier_options                    --mode clausify
% 11.93/2.00  --stdin                                 false
% 11.93/2.00  --stats_out                             all
% 11.93/2.00  
% 11.93/2.00  ------ General Options
% 11.93/2.00  
% 11.93/2.00  --fof                                   false
% 11.93/2.00  --time_out_real                         305.
% 11.93/2.00  --time_out_virtual                      -1.
% 11.93/2.00  --symbol_type_check                     false
% 11.93/2.00  --clausify_out                          false
% 11.93/2.00  --sig_cnt_out                           false
% 11.93/2.00  --trig_cnt_out                          false
% 11.93/2.00  --trig_cnt_out_tolerance                1.
% 11.93/2.00  --trig_cnt_out_sk_spl                   false
% 11.93/2.00  --abstr_cl_out                          false
% 11.93/2.00  
% 11.93/2.00  ------ Global Options
% 11.93/2.00  
% 11.93/2.00  --schedule                              default
% 11.93/2.00  --add_important_lit                     false
% 11.93/2.00  --prop_solver_per_cl                    1000
% 11.93/2.00  --min_unsat_core                        false
% 11.93/2.00  --soft_assumptions                      false
% 11.93/2.00  --soft_lemma_size                       3
% 11.93/2.00  --prop_impl_unit_size                   0
% 11.93/2.00  --prop_impl_unit                        []
% 11.93/2.00  --share_sel_clauses                     true
% 11.93/2.00  --reset_solvers                         false
% 11.93/2.00  --bc_imp_inh                            [conj_cone]
% 11.93/2.00  --conj_cone_tolerance                   3.
% 11.93/2.00  --extra_neg_conj                        none
% 11.93/2.00  --large_theory_mode                     true
% 11.93/2.00  --prolific_symb_bound                   200
% 11.93/2.00  --lt_threshold                          2000
% 11.93/2.00  --clause_weak_htbl                      true
% 11.93/2.00  --gc_record_bc_elim                     false
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing Options
% 11.93/2.00  
% 11.93/2.00  --preprocessing_flag                    true
% 11.93/2.00  --time_out_prep_mult                    0.1
% 11.93/2.00  --splitting_mode                        input
% 11.93/2.00  --splitting_grd                         true
% 11.93/2.00  --splitting_cvd                         false
% 11.93/2.00  --splitting_cvd_svl                     false
% 11.93/2.00  --splitting_nvd                         32
% 11.93/2.00  --sub_typing                            true
% 11.93/2.00  --prep_gs_sim                           true
% 11.93/2.00  --prep_unflatten                        true
% 11.93/2.00  --prep_res_sim                          true
% 11.93/2.00  --prep_upred                            true
% 11.93/2.00  --prep_sem_filter                       exhaustive
% 11.93/2.00  --prep_sem_filter_out                   false
% 11.93/2.00  --pred_elim                             true
% 11.93/2.00  --res_sim_input                         true
% 11.93/2.00  --eq_ax_congr_red                       true
% 11.93/2.00  --pure_diseq_elim                       true
% 11.93/2.00  --brand_transform                       false
% 11.93/2.00  --non_eq_to_eq                          false
% 11.93/2.00  --prep_def_merge                        true
% 11.93/2.00  --prep_def_merge_prop_impl              false
% 11.93/2.00  --prep_def_merge_mbd                    true
% 11.93/2.00  --prep_def_merge_tr_red                 false
% 11.93/2.00  --prep_def_merge_tr_cl                  false
% 11.93/2.00  --smt_preprocessing                     true
% 11.93/2.00  --smt_ac_axioms                         fast
% 11.93/2.00  --preprocessed_out                      false
% 11.93/2.00  --preprocessed_stats                    false
% 11.93/2.00  
% 11.93/2.00  ------ Abstraction refinement Options
% 11.93/2.00  
% 11.93/2.00  --abstr_ref                             []
% 11.93/2.00  --abstr_ref_prep                        false
% 11.93/2.00  --abstr_ref_until_sat                   false
% 11.93/2.00  --abstr_ref_sig_restrict                funpre
% 11.93/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.93/2.00  --abstr_ref_under                       []
% 11.93/2.00  
% 11.93/2.00  ------ SAT Options
% 11.93/2.00  
% 11.93/2.00  --sat_mode                              false
% 11.93/2.00  --sat_fm_restart_options                ""
% 11.93/2.00  --sat_gr_def                            false
% 11.93/2.00  --sat_epr_types                         true
% 11.93/2.00  --sat_non_cyclic_types                  false
% 11.93/2.00  --sat_finite_models                     false
% 11.93/2.00  --sat_fm_lemmas                         false
% 11.93/2.00  --sat_fm_prep                           false
% 11.93/2.00  --sat_fm_uc_incr                        true
% 11.93/2.00  --sat_out_model                         small
% 11.93/2.00  --sat_out_clauses                       false
% 11.93/2.00  
% 11.93/2.00  ------ QBF Options
% 11.93/2.00  
% 11.93/2.00  --qbf_mode                              false
% 11.93/2.00  --qbf_elim_univ                         false
% 11.93/2.00  --qbf_dom_inst                          none
% 11.93/2.00  --qbf_dom_pre_inst                      false
% 11.93/2.00  --qbf_sk_in                             false
% 11.93/2.00  --qbf_pred_elim                         true
% 11.93/2.00  --qbf_split                             512
% 11.93/2.00  
% 11.93/2.00  ------ BMC1 Options
% 11.93/2.00  
% 11.93/2.00  --bmc1_incremental                      false
% 11.93/2.00  --bmc1_axioms                           reachable_all
% 11.93/2.00  --bmc1_min_bound                        0
% 11.93/2.00  --bmc1_max_bound                        -1
% 11.93/2.00  --bmc1_max_bound_default                -1
% 11.93/2.00  --bmc1_symbol_reachability              true
% 11.93/2.00  --bmc1_property_lemmas                  false
% 11.93/2.00  --bmc1_k_induction                      false
% 11.93/2.00  --bmc1_non_equiv_states                 false
% 11.93/2.00  --bmc1_deadlock                         false
% 11.93/2.00  --bmc1_ucm                              false
% 11.93/2.00  --bmc1_add_unsat_core                   none
% 11.93/2.00  --bmc1_unsat_core_children              false
% 11.93/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.93/2.00  --bmc1_out_stat                         full
% 11.93/2.00  --bmc1_ground_init                      false
% 11.93/2.00  --bmc1_pre_inst_next_state              false
% 11.93/2.00  --bmc1_pre_inst_state                   false
% 11.93/2.00  --bmc1_pre_inst_reach_state             false
% 11.93/2.00  --bmc1_out_unsat_core                   false
% 11.93/2.00  --bmc1_aig_witness_out                  false
% 11.93/2.00  --bmc1_verbose                          false
% 11.93/2.00  --bmc1_dump_clauses_tptp                false
% 11.93/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.93/2.00  --bmc1_dump_file                        -
% 11.93/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.93/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.93/2.00  --bmc1_ucm_extend_mode                  1
% 11.93/2.00  --bmc1_ucm_init_mode                    2
% 11.93/2.00  --bmc1_ucm_cone_mode                    none
% 11.93/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.93/2.00  --bmc1_ucm_relax_model                  4
% 11.93/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.93/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.93/2.00  --bmc1_ucm_layered_model                none
% 11.93/2.00  --bmc1_ucm_max_lemma_size               10
% 11.93/2.00  
% 11.93/2.00  ------ AIG Options
% 11.93/2.00  
% 11.93/2.00  --aig_mode                              false
% 11.93/2.00  
% 11.93/2.00  ------ Instantiation Options
% 11.93/2.00  
% 11.93/2.00  --instantiation_flag                    true
% 11.93/2.00  --inst_sos_flag                         false
% 11.93/2.00  --inst_sos_phase                        true
% 11.93/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.93/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.93/2.00  --inst_lit_sel_side                     none
% 11.93/2.00  --inst_solver_per_active                1400
% 11.93/2.00  --inst_solver_calls_frac                1.
% 11.93/2.00  --inst_passive_queue_type               priority_queues
% 11.93/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.93/2.00  --inst_passive_queues_freq              [25;2]
% 11.93/2.00  --inst_dismatching                      true
% 11.93/2.00  --inst_eager_unprocessed_to_passive     true
% 11.93/2.00  --inst_prop_sim_given                   true
% 11.93/2.00  --inst_prop_sim_new                     false
% 11.93/2.00  --inst_subs_new                         false
% 11.93/2.00  --inst_eq_res_simp                      false
% 11.93/2.00  --inst_subs_given                       false
% 11.93/2.00  --inst_orphan_elimination               true
% 11.93/2.00  --inst_learning_loop_flag               true
% 11.93/2.00  --inst_learning_start                   3000
% 11.93/2.00  --inst_learning_factor                  2
% 11.93/2.00  --inst_start_prop_sim_after_learn       3
% 11.93/2.00  --inst_sel_renew                        solver
% 11.93/2.00  --inst_lit_activity_flag                true
% 11.93/2.00  --inst_restr_to_given                   false
% 11.93/2.00  --inst_activity_threshold               500
% 11.93/2.00  --inst_out_proof                        true
% 11.93/2.00  
% 11.93/2.00  ------ Resolution Options
% 11.93/2.00  
% 11.93/2.00  --resolution_flag                       false
% 11.93/2.00  --res_lit_sel                           adaptive
% 11.93/2.00  --res_lit_sel_side                      none
% 11.93/2.00  --res_ordering                          kbo
% 11.93/2.00  --res_to_prop_solver                    active
% 11.93/2.00  --res_prop_simpl_new                    false
% 11.93/2.00  --res_prop_simpl_given                  true
% 11.93/2.00  --res_passive_queue_type                priority_queues
% 11.93/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.93/2.00  --res_passive_queues_freq               [15;5]
% 11.93/2.00  --res_forward_subs                      full
% 11.93/2.00  --res_backward_subs                     full
% 11.93/2.00  --res_forward_subs_resolution           true
% 11.93/2.00  --res_backward_subs_resolution          true
% 11.93/2.00  --res_orphan_elimination                true
% 11.93/2.00  --res_time_limit                        2.
% 11.93/2.00  --res_out_proof                         true
% 11.93/2.00  
% 11.93/2.00  ------ Superposition Options
% 11.93/2.00  
% 11.93/2.00  --superposition_flag                    true
% 11.93/2.00  --sup_passive_queue_type                priority_queues
% 11.93/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.93/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.93/2.00  --demod_completeness_check              fast
% 11.93/2.00  --demod_use_ground                      true
% 11.93/2.00  --sup_to_prop_solver                    passive
% 11.93/2.00  --sup_prop_simpl_new                    true
% 11.93/2.00  --sup_prop_simpl_given                  true
% 11.93/2.00  --sup_fun_splitting                     false
% 11.93/2.00  --sup_smt_interval                      50000
% 11.93/2.00  
% 11.93/2.00  ------ Superposition Simplification Setup
% 11.93/2.00  
% 11.93/2.00  --sup_indices_passive                   []
% 11.93/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.93/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_full_bw                           [BwDemod]
% 11.93/2.00  --sup_immed_triv                        [TrivRules]
% 11.93/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.93/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_immed_bw_main                     []
% 11.93/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.93/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.93/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.93/2.00  
% 11.93/2.00  ------ Combination Options
% 11.93/2.00  
% 11.93/2.00  --comb_res_mult                         3
% 11.93/2.00  --comb_sup_mult                         2
% 11.93/2.00  --comb_inst_mult                        10
% 11.93/2.00  
% 11.93/2.00  ------ Debug Options
% 11.93/2.00  
% 11.93/2.00  --dbg_backtrace                         false
% 11.93/2.00  --dbg_dump_prop_clauses                 false
% 11.93/2.00  --dbg_dump_prop_clauses_file            -
% 11.93/2.00  --dbg_out_stat                          false
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ Proving...
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  % SZS status Theorem for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  fof(f4,axiom,(
% 11.93/2.00    ! [X0,X1,X2] : ((l3_lattices(X2) & v17_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) => (r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))))),
% 11.93/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f14,plain,(
% 11.93/2.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))) | (~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)))),
% 11.93/2.00    inference(ennf_transformation,[],[f4])).
% 11.93/2.00  
% 11.93/2.00  fof(f15,plain,(
% 11.93/2.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 11.93/2.00    inference(flattening,[],[f14])).
% 11.93/2.00  
% 11.93/2.00  fof(f24,plain,(
% 11.93/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 11.93/2.00    inference(nnf_transformation,[],[f15])).
% 11.93/2.00  
% 11.93/2.00  fof(f25,plain,(
% 11.93/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X4] : (r2_hidden(X4,X1) & k7_lattices(X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 11.93/2.00    inference(rectify,[],[f24])).
% 11.93/2.00  
% 11.93/2.00  fof(f26,plain,(
% 11.93/2.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & k7_lattices(X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & k7_lattices(X2,sK1(X0,X1,X2)) = X0 & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2))))),
% 11.93/2.00    introduced(choice_axiom,[])).
% 11.93/2.00  
% 11.93/2.00  fof(f27,plain,(
% 11.93/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & k7_lattices(X2,sK1(X0,X1,X2)) = X0 & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 11.93/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 11.93/2.00  
% 11.93/2.00  fof(f43,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f27])).
% 11.93/2.00  
% 11.93/2.00  fof(f53,plain,(
% 11.93/2.00    ( ! [X2,X3,X1] : (r2_hidden(k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 11.93/2.00    inference(equality_resolution,[],[f43])).
% 11.93/2.00  
% 11.93/2.00  fof(f6,conjecture,(
% 11.93/2.00    ! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r3_lattice3(X1,X2,X0) <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 11.93/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f7,negated_conjecture,(
% 11.93/2.00    ~! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r3_lattice3(X1,X2,X0) <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 11.93/2.00    inference(negated_conjecture,[],[f6])).
% 11.93/2.00  
% 11.93/2.00  fof(f18,plain,(
% 11.93/2.00    ? [X0,X1] : (? [X2] : ((r3_lattice3(X1,X2,X0) <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & m1_subset_1(X2,u1_struct_0(X1))) & (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)))),
% 11.93/2.00    inference(ennf_transformation,[],[f7])).
% 11.93/2.00  
% 11.93/2.00  fof(f19,plain,(
% 11.93/2.00    ? [X0,X1] : (? [X2] : ((r3_lattice3(X1,X2,X0) <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 11.93/2.00    inference(flattening,[],[f18])).
% 11.93/2.00  
% 11.93/2.00  fof(f29,plain,(
% 11.93/2.00    ? [X0,X1] : (? [X2] : (((~r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r3_lattice3(X1,X2,X0)) & (r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r3_lattice3(X1,X2,X0))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 11.93/2.00    inference(nnf_transformation,[],[f19])).
% 11.93/2.00  
% 11.93/2.00  fof(f30,plain,(
% 11.93/2.00    ? [X0,X1] : (? [X2] : ((~r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r3_lattice3(X1,X2,X0)) & (r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r3_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 11.93/2.00    inference(flattening,[],[f29])).
% 11.93/2.00  
% 11.93/2.00  fof(f32,plain,(
% 11.93/2.00    ( ! [X0,X1] : (? [X2] : ((~r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r3_lattice3(X1,X2,X0)) & (r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r3_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) => ((~r4_lattice3(X1,k7_lattices(X1,sK4),a_2_0_lattice3(X0,X1)) | ~r3_lattice3(X1,sK4,X0)) & (r4_lattice3(X1,k7_lattices(X1,sK4),a_2_0_lattice3(X0,X1)) | r3_lattice3(X1,sK4,X0)) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 11.93/2.00    introduced(choice_axiom,[])).
% 11.93/2.00  
% 11.93/2.00  fof(f31,plain,(
% 11.93/2.00    ? [X0,X1] : (? [X2] : ((~r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r3_lattice3(X1,X2,X0)) & (r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r3_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (? [X2] : ((~r4_lattice3(sK3,k7_lattices(sK3,X2),a_2_0_lattice3(sK2,sK3)) | ~r3_lattice3(sK3,X2,sK2)) & (r4_lattice3(sK3,k7_lattices(sK3,X2),a_2_0_lattice3(sK2,sK3)) | r3_lattice3(sK3,X2,sK2)) & m1_subset_1(X2,u1_struct_0(sK3))) & l3_lattices(sK3) & v17_lattices(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 11.93/2.00    introduced(choice_axiom,[])).
% 11.93/2.00  
% 11.93/2.00  fof(f33,plain,(
% 11.93/2.00    ((~r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3)) | ~r3_lattice3(sK3,sK4,sK2)) & (r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3)) | r3_lattice3(sK3,sK4,sK2)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v17_lattices(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 11.93/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f32,f31])).
% 11.93/2.00  
% 11.93/2.00  fof(f48,plain,(
% 11.93/2.00    v17_lattices(sK3)),
% 11.93/2.00    inference(cnf_transformation,[],[f33])).
% 11.93/2.00  
% 11.93/2.00  fof(f46,plain,(
% 11.93/2.00    ~v2_struct_0(sK3)),
% 11.93/2.00    inference(cnf_transformation,[],[f33])).
% 11.93/2.00  
% 11.93/2.00  fof(f47,plain,(
% 11.93/2.00    v10_lattices(sK3)),
% 11.93/2.00    inference(cnf_transformation,[],[f33])).
% 11.93/2.00  
% 11.93/2.00  fof(f49,plain,(
% 11.93/2.00    l3_lattices(sK3)),
% 11.93/2.00    inference(cnf_transformation,[],[f33])).
% 11.93/2.00  
% 11.93/2.00  fof(f50,plain,(
% 11.93/2.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 11.93/2.00    inference(cnf_transformation,[],[f33])).
% 11.93/2.00  
% 11.93/2.00  fof(f3,axiom,(
% 11.93/2.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 11.93/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f12,plain,(
% 11.93/2.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.93/2.00    inference(ennf_transformation,[],[f3])).
% 11.93/2.00  
% 11.93/2.00  fof(f13,plain,(
% 11.93/2.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.93/2.00    inference(flattening,[],[f12])).
% 11.93/2.00  
% 11.93/2.00  fof(f20,plain,(
% 11.93/2.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.93/2.00    inference(nnf_transformation,[],[f13])).
% 11.93/2.00  
% 11.93/2.00  fof(f21,plain,(
% 11.93/2.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.93/2.00    inference(rectify,[],[f20])).
% 11.93/2.00  
% 11.93/2.00  fof(f22,plain,(
% 11.93/2.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 11.93/2.00    introduced(choice_axiom,[])).
% 11.93/2.00  
% 11.93/2.00  fof(f23,plain,(
% 11.93/2.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.93/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 11.93/2.00  
% 11.93/2.00  fof(f37,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f23])).
% 11.93/2.00  
% 11.93/2.00  fof(f2,axiom,(
% 11.93/2.00    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 11.93/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f10,plain,(
% 11.93/2.00    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.93/2.00    inference(ennf_transformation,[],[f2])).
% 11.93/2.00  
% 11.93/2.00  fof(f11,plain,(
% 11.93/2.00    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.93/2.00    inference(flattening,[],[f10])).
% 11.93/2.00  
% 11.93/2.00  fof(f35,plain,(
% 11.93/2.00    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f11])).
% 11.93/2.00  
% 11.93/2.00  fof(f38,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f23])).
% 11.93/2.00  
% 11.93/2.00  fof(f42,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f27])).
% 11.93/2.00  
% 11.93/2.00  fof(f41,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (k7_lattices(X2,sK1(X0,X1,X2)) = X0 | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f27])).
% 11.93/2.00  
% 11.93/2.00  fof(f5,axiom,(
% 11.93/2.00    ! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 11.93/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f16,plain,(
% 11.93/2.00    ! [X0,X1] : (! [X2] : ((r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 11.93/2.00    inference(ennf_transformation,[],[f5])).
% 11.93/2.00  
% 11.93/2.00  fof(f17,plain,(
% 11.93/2.00    ! [X0,X1] : (! [X2] : ((r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.93/2.00    inference(flattening,[],[f16])).
% 11.93/2.00  
% 11.93/2.00  fof(f28,plain,(
% 11.93/2.00    ! [X0,X1] : (! [X2] : (((r4_lattice3(X1,X2,X0) | ~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.93/2.00    inference(nnf_transformation,[],[f17])).
% 11.93/2.00  
% 11.93/2.00  fof(f45,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (r4_lattice3(X1,X2,X0) | ~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f28])).
% 11.93/2.00  
% 11.93/2.00  fof(f52,plain,(
% 11.93/2.00    ~r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3)) | ~r3_lattice3(sK3,sK4,sK2)),
% 11.93/2.00    inference(cnf_transformation,[],[f33])).
% 11.93/2.00  
% 11.93/2.00  fof(f1,axiom,(
% 11.93/2.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 11.93/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f8,plain,(
% 11.93/2.00    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.93/2.00    inference(ennf_transformation,[],[f1])).
% 11.93/2.00  
% 11.93/2.00  fof(f9,plain,(
% 11.93/2.00    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.93/2.00    inference(flattening,[],[f8])).
% 11.93/2.00  
% 11.93/2.00  fof(f34,plain,(
% 11.93/2.00    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f9])).
% 11.93/2.00  
% 11.93/2.00  fof(f39,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f23])).
% 11.93/2.00  
% 11.93/2.00  fof(f36,plain,(
% 11.93/2.00    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f23])).
% 11.93/2.00  
% 11.93/2.00  fof(f40,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2)) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f27])).
% 11.93/2.00  
% 11.93/2.00  fof(f44,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f28])).
% 11.93/2.00  
% 11.93/2.00  fof(f51,plain,(
% 11.93/2.00    r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3)) | r3_lattice3(sK3,sK4,sK2)),
% 11.93/2.00    inference(cnf_transformation,[],[f33])).
% 11.93/2.00  
% 11.93/2.00  cnf(c_6,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,X1)
% 11.93/2.00      | r2_hidden(k7_lattices(X2,X0),a_2_0_lattice3(X1,X2))
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 11.93/2.00      | ~ v10_lattices(X2)
% 11.93/2.00      | ~ v17_lattices(X2)
% 11.93/2.00      | v2_struct_0(X2)
% 11.93/2.00      | ~ l3_lattices(X2) ),
% 11.93/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_16,negated_conjecture,
% 11.93/2.00      ( v17_lattices(sK3) ),
% 11.93/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_410,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,X1)
% 11.93/2.00      | r2_hidden(k7_lattices(X2,X0),a_2_0_lattice3(X1,X2))
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 11.93/2.00      | ~ v10_lattices(X2)
% 11.93/2.00      | v2_struct_0(X2)
% 11.93/2.00      | ~ l3_lattices(X2)
% 11.93/2.00      | sK3 != X2 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_411,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,X1)
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,X0),a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | ~ v10_lattices(sK3)
% 11.93/2.00      | v2_struct_0(sK3)
% 11.93/2.00      | ~ l3_lattices(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_410]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_18,negated_conjecture,
% 11.93/2.00      ( ~ v2_struct_0(sK3) ),
% 11.93/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_17,negated_conjecture,
% 11.93/2.00      ( v10_lattices(sK3) ),
% 11.93/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_15,negated_conjecture,
% 11.93/2.00      ( l3_lattices(sK3) ),
% 11.93/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_415,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,X0),a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | ~ r2_hidden(X0,X1) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_411,c_18,c_17,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_416,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,X1)
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,X0),a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_415]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_635,plain,
% 11.93/2.00      ( ~ r2_hidden(X0_45,X0_48)
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,X0_45),a_2_0_lattice3(X0_48,sK3))
% 11.93/2.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_416]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_983,plain,
% 11.93/2.00      ( r2_hidden(X0_45,X0_48) != iProver_top
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,X0_45),a_2_0_lattice3(X0_48,sK3)) = iProver_top
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_14,negated_conjecture,
% 11.93/2.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_642,negated_conjecture,
% 11.93/2.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_14]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_976,plain,
% 11.93/2.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_4,plain,
% 11.93/2.00      ( r3_lattice3(X0,X1,X2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0) ),
% 11.93/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_467,plain,
% 11.93/2.00      ( r3_lattice3(X0,X1,X2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | sK3 != X0 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_468,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0,X1)
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
% 11.93/2.00      | v2_struct_0(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_467]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_472,plain,
% 11.93/2.00      ( m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | r3_lattice3(sK3,X0,X1) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_468,c_18]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_473,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0,X1)
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_472]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_633,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0_45,X0_48)
% 11.93/2.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK3))
% 11.93/2.00      | m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_473]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_985,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top
% 11.93/2.00      | m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3)) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.93/2.00      | ~ v10_lattices(X1)
% 11.93/2.00      | ~ v17_lattices(X1)
% 11.93/2.00      | v2_struct_0(X1)
% 11.93/2.00      | ~ l3_lattices(X1)
% 11.93/2.00      | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
% 11.93/2.00      inference(cnf_transformation,[],[f35]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_338,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.93/2.00      | ~ v10_lattices(X1)
% 11.93/2.00      | v2_struct_0(X1)
% 11.93/2.00      | ~ l3_lattices(X1)
% 11.93/2.00      | k7_lattices(X1,k7_lattices(X1,X0)) = X0
% 11.93/2.00      | sK3 != X1 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_339,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | ~ v10_lattices(sK3)
% 11.93/2.00      | v2_struct_0(sK3)
% 11.93/2.00      | ~ l3_lattices(sK3)
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,X0)) = X0 ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_338]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_343,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,X0)) = X0 ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_339,c_18,c_17,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_639,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,X0_45)) = X0_45 ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_343]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_979,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,X0_45)) = X0_45
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1524,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK0(sK3,X0_45,X0_48))) = sK0(sK3,X0_45,X0_48)
% 11.93/2.00      | r3_lattice3(sK3,X0_45,X0_48) = iProver_top
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_985,c_979]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_2635,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK0(sK3,sK4,X0_48))) = sK0(sK3,sK4,X0_48)
% 11.93/2.00      | r3_lattice3(sK3,sK4,X0_48) = iProver_top ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_976,c_1524]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3,plain,
% 11.93/2.00      ( r3_lattice3(X0,X1,X2)
% 11.93/2.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0) ),
% 11.93/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_488,plain,
% 11.93/2.00      ( r3_lattice3(X0,X1,X2)
% 11.93/2.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | sK3 != X0 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_489,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0,X1)
% 11.93/2.00      | r2_hidden(sK0(sK3,X0,X1),X1)
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | v2_struct_0(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_488]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_493,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | r2_hidden(sK0(sK3,X0,X1),X1)
% 11.93/2.00      | r3_lattice3(sK3,X0,X1) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_489,c_18]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_494,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0,X1)
% 11.93/2.00      | r2_hidden(sK0(sK3,X0,X1),X1)
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_493]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_632,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0_45,X0_48)
% 11.93/2.00      | r2_hidden(sK0(sK3,X0_45,X0_48),X0_48)
% 11.93/2.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_494]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_986,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,X0_45,X0_48),X0_48) = iProver_top
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_7,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 11.93/2.00      | r2_hidden(sK1(X0,X1,X2),X1)
% 11.93/2.00      | ~ v10_lattices(X2)
% 11.93/2.00      | ~ v17_lattices(X2)
% 11.93/2.00      | v2_struct_0(X2)
% 11.93/2.00      | ~ l3_lattices(X2) ),
% 11.93/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_392,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 11.93/2.00      | r2_hidden(sK1(X0,X1,X2),X1)
% 11.93/2.00      | ~ v10_lattices(X2)
% 11.93/2.00      | v2_struct_0(X2)
% 11.93/2.00      | ~ l3_lattices(X2)
% 11.93/2.00      | sK3 != X2 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_393,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | r2_hidden(sK1(X0,X1,sK3),X1)
% 11.93/2.00      | ~ v10_lattices(sK3)
% 11.93/2.00      | v2_struct_0(sK3)
% 11.93/2.00      | ~ l3_lattices(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_392]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_397,plain,
% 11.93/2.00      ( r2_hidden(sK1(X0,X1,sK3),X1)
% 11.93/2.00      | ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3)) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_393,c_18,c_17,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_398,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | r2_hidden(sK1(X0,X1,sK3),X1) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_397]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_636,plain,
% 11.93/2.00      ( ~ r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3))
% 11.93/2.00      | r2_hidden(sK1(X0_45,X0_48,sK3),X0_48) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_398]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_982,plain,
% 11.93/2.00      ( r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3)) != iProver_top
% 11.93/2.00      | r2_hidden(sK1(X0_45,X0_48,sK3),X0_48) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_8,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 11.93/2.00      | ~ v10_lattices(X2)
% 11.93/2.00      | ~ v17_lattices(X2)
% 11.93/2.00      | v2_struct_0(X2)
% 11.93/2.00      | ~ l3_lattices(X2)
% 11.93/2.00      | k7_lattices(X2,sK1(X0,X1,X2)) = X0 ),
% 11.93/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_374,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 11.93/2.00      | ~ v10_lattices(X2)
% 11.93/2.00      | v2_struct_0(X2)
% 11.93/2.00      | ~ l3_lattices(X2)
% 11.93/2.00      | k7_lattices(X2,sK1(X0,X1,X2)) = X0
% 11.93/2.00      | sK3 != X2 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_375,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | ~ v10_lattices(sK3)
% 11.93/2.00      | v2_struct_0(sK3)
% 11.93/2.00      | ~ l3_lattices(sK3)
% 11.93/2.00      | k7_lattices(sK3,sK1(X0,X1,sK3)) = X0 ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_374]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_379,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | k7_lattices(sK3,sK1(X0,X1,sK3)) = X0 ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_375,c_18,c_17,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_637,plain,
% 11.93/2.00      ( ~ r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3))
% 11.93/2.00      | k7_lattices(sK3,sK1(X0_45,X0_48,sK3)) = X0_45 ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_379]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_981,plain,
% 11.93/2.00      ( k7_lattices(sK3,sK1(X0_45,X0_48,sK3)) = X0_45
% 11.93/2.00      | r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1185,plain,
% 11.93/2.00      ( k7_lattices(sK3,sK1(sK1(X0_45,a_2_0_lattice3(X0_48,sK3),sK3),X0_48,sK3)) = sK1(X0_45,a_2_0_lattice3(X0_48,sK3),sK3)
% 11.93/2.00      | r2_hidden(X0_45,a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)) != iProver_top ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_982,c_981]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1851,plain,
% 11.93/2.00      ( k7_lattices(sK3,sK1(sK1(sK0(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)),a_2_0_lattice3(X0_48,sK3),sK3),X0_48,sK3)) = sK1(sK0(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)),a_2_0_lattice3(X0_48,sK3),sK3)
% 11.93/2.00      | r3_lattice3(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)) = iProver_top
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_986,c_1185]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_10,plain,
% 11.93/2.00      ( r4_lattice3(X0,X1,X2)
% 11.93/2.00      | ~ r3_lattice3(X0,k7_lattices(X0,X1),a_2_0_lattice3(X2,X0))
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | ~ v10_lattices(X0)
% 11.93/2.00      | ~ v17_lattices(X0)
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0) ),
% 11.93/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_12,negated_conjecture,
% 11.93/2.00      ( ~ r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
% 11.93/2.00      | ~ r3_lattice3(sK3,sK4,sK2) ),
% 11.93/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_140,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3)) ),
% 11.93/2.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_141,plain,
% 11.93/2.00      ( ~ r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
% 11.93/2.00      | ~ r3_lattice3(sK3,sK4,sK2) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_140]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_296,plain,
% 11.93/2.00      ( ~ r3_lattice3(X0,k7_lattices(X0,X1),a_2_0_lattice3(X2,X0))
% 11.93/2.00      | ~ r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | ~ v10_lattices(X0)
% 11.93/2.00      | ~ v17_lattices(X0)
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0)
% 11.93/2.00      | a_2_0_lattice3(sK2,sK3) != X2
% 11.93/2.00      | k7_lattices(sK3,sK4) != X1
% 11.93/2.00      | sK3 != X0 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_10,c_141]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_297,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | ~ r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3))
% 11.93/2.00      | ~ v10_lattices(sK3)
% 11.93/2.00      | ~ v17_lattices(sK3)
% 11.93/2.00      | v2_struct_0(sK3)
% 11.93/2.00      | ~ l3_lattices(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_296]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_299,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | ~ r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_297,c_18,c_17,c_16,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_641,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | ~ r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_299]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_977,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) != iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_23,plain,
% 11.93/2.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_301,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) != iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_0,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.93/2.00      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 11.93/2.00      | v2_struct_0(X1)
% 11.93/2.00      | ~ l3_lattices(X1) ),
% 11.93/2.00      inference(cnf_transformation,[],[f34]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_509,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.93/2.00      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 11.93/2.00      | v2_struct_0(X1)
% 11.93/2.00      | sK3 != X1 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_510,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,X0),u1_struct_0(sK3))
% 11.93/2.00      | v2_struct_0(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_509]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_514,plain,
% 11.93/2.00      ( m1_subset_1(k7_lattices(sK3,X0),u1_struct_0(sK3))
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_510,c_18]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_515,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,X0),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_514]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_631,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,X0_45),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_515]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_681,plain,
% 11.93/2.00      ( m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,X0_45),u1_struct_0(sK3)) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_683,plain,
% 11.93/2.00      ( m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) = iProver_top
% 11.93/2.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_681]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1273,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,sK2) != iProver_top
% 11.93/2.00      | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_977,c_23,c_301,c_683]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1274,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) != iProver_top ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_1273]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1080,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK4)) = sK4 ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_976,c_979]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1277,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) != iProver_top ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_1274,c_1080]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_12420,plain,
% 11.93/2.00      ( k7_lattices(sK3,sK1(sK1(sK0(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)) = sK1(sK0(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) != iProver_top
% 11.93/2.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_1851,c_1277]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_660,plain,
% 11.93/2.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,sK4)) = sK4 ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_639]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_2,plain,
% 11.93/2.00      ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 11.93/2.00      | r3_lattice3(X0,X1,X2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0) ),
% 11.93/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_5,plain,
% 11.93/2.00      ( r1_lattices(X0,X1,X2)
% 11.93/2.00      | ~ r3_lattice3(X0,X1,X3)
% 11.93/2.00      | ~ r2_hidden(X2,X3)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0) ),
% 11.93/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_262,plain,
% 11.93/2.00      ( ~ r3_lattice3(X0,X1,X2)
% 11.93/2.00      | r3_lattice3(X3,X4,X5)
% 11.93/2.00      | ~ r2_hidden(X6,X2)
% 11.93/2.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | ~ m1_subset_1(X6,u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X3)
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X3)
% 11.93/2.00      | ~ l3_lattices(X0)
% 11.93/2.00      | X0 != X3
% 11.93/2.00      | X1 != X4
% 11.93/2.00      | sK0(X3,X4,X5) != X6 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_263,plain,
% 11.93/2.00      ( ~ r3_lattice3(X0,X1,X2)
% 11.93/2.00      | r3_lattice3(X0,X1,X3)
% 11.93/2.00      | ~ r2_hidden(sK0(X0,X1,X3),X2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | ~ m1_subset_1(sK0(X0,X1,X3),u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_262]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_279,plain,
% 11.93/2.00      ( ~ r3_lattice3(X0,X1,X2)
% 11.93/2.00      | r3_lattice3(X0,X1,X3)
% 11.93/2.00      | ~ r2_hidden(sK0(X0,X1,X3),X2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0) ),
% 11.93/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_263,c_4]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_447,plain,
% 11.93/2.00      ( ~ r3_lattice3(X0,X1,X2)
% 11.93/2.00      | r3_lattice3(X0,X1,X3)
% 11.93/2.00      | ~ r2_hidden(sK0(X0,X1,X3),X2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | sK3 != X0 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_279,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_448,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,X0,X1)
% 11.93/2.00      | r3_lattice3(sK3,X0,X2)
% 11.93/2.00      | ~ r2_hidden(sK0(sK3,X0,X2),X1)
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | v2_struct_0(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_447]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_450,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.93/2.00      | ~ r2_hidden(sK0(sK3,X0,X2),X1)
% 11.93/2.00      | r3_lattice3(sK3,X0,X2)
% 11.93/2.00      | ~ r3_lattice3(sK3,X0,X1) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_448,c_18]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_451,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,X0,X1)
% 11.93/2.00      | r3_lattice3(sK3,X0,X2)
% 11.93/2.00      | ~ r2_hidden(sK0(sK3,X0,X2),X1)
% 11.93/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_450]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_634,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,X0_45,X0_48)
% 11.93/2.00      | r3_lattice3(sK3,X0_45,X1_48)
% 11.93/2.00      | ~ r2_hidden(sK0(sK3,X0_45,X1_48),X0_48)
% 11.93/2.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_451]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1081,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),X0_48)
% 11.93/2.00      | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | ~ r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),X0_48)
% 11.93/2.00      | ~ m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_634]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1082,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),X0_48) != iProver_top
% 11.93/2.00      | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),X0_48) != iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1084,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),sK2) != iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),sK2) != iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_1082]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1086,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | ~ m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_632]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1090,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1086]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1128,plain,
% 11.93/2.00      ( r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3))
% 11.93/2.00      | ~ r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_636]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1132,plain,
% 11.93/2.00      ( r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) = iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1127,plain,
% 11.93/2.00      ( ~ r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) = sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_637]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1134,plain,
% 11.93/2.00      ( k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) = sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_647,plain,
% 11.93/2.00      ( ~ m1_subset_1(X0_45,X0_46)
% 11.93/2.00      | m1_subset_1(X1_45,X0_46)
% 11.93/2.00      | X1_45 != X0_45 ),
% 11.93/2.00      theory(equality) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1092,plain,
% 11.93/2.00      ( m1_subset_1(X0_45,u1_struct_0(sK3))
% 11.93/2.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.93/2.00      | X0_45 != sK4 ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_647]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1137,plain,
% 11.93/2.00      ( m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3))
% 11.93/2.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,sK4)) != sK4 ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_1092]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1138,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK4)) != sK4
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,k7_lattices(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
% 11.93/2.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_644,plain,( X0_45 = X0_45 ),theory(equality) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1384,plain,
% 11.93/2.00      ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_644]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_9,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 11.93/2.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2))
% 11.93/2.00      | ~ v10_lattices(X2)
% 11.93/2.00      | ~ v17_lattices(X2)
% 11.93/2.00      | v2_struct_0(X2)
% 11.93/2.00      | ~ l3_lattices(X2) ),
% 11.93/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_356,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
% 11.93/2.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X2))
% 11.93/2.00      | ~ v10_lattices(X2)
% 11.93/2.00      | v2_struct_0(X2)
% 11.93/2.00      | ~ l3_lattices(X2)
% 11.93/2.00      | sK3 != X2 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_357,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | m1_subset_1(sK1(X0,X1,sK3),u1_struct_0(sK3))
% 11.93/2.00      | ~ v10_lattices(sK3)
% 11.93/2.00      | v2_struct_0(sK3)
% 11.93/2.00      | ~ l3_lattices(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_356]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_361,plain,
% 11.93/2.00      ( m1_subset_1(sK1(X0,X1,sK3),u1_struct_0(sK3))
% 11.93/2.00      | ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3)) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_357,c_18,c_17,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_362,plain,
% 11.93/2.00      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,sK3))
% 11.93/2.00      | m1_subset_1(sK1(X0,X1,sK3),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_361]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_638,plain,
% 11.93/2.00      ( ~ r2_hidden(X0_45,a_2_0_lattice3(X0_48,sK3))
% 11.93/2.00      | m1_subset_1(sK1(X0_45,X0_48,sK3),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_362]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1631,plain,
% 11.93/2.00      ( ~ r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3))
% 11.93/2.00      | m1_subset_1(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_638]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1632,plain,
% 11.93/2.00      ( r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) != iProver_top
% 11.93/2.00      | m1_subset_1(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),u1_struct_0(sK3)) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1631]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1630,plain,
% 11.93/2.00      ( r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2)
% 11.93/2.00      | ~ r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_636]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1634,plain,
% 11.93/2.00      ( r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2) = iProver_top
% 11.93/2.00      | r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1630]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1629,plain,
% 11.93/2.00      ( ~ r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3))
% 11.93/2.00      | k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)) = sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_637]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1636,plain,
% 11.93/2.00      ( k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)) = sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)
% 11.93/2.00      | r2_hidden(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),a_2_0_lattice3(sK2,sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1629]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_648,plain,
% 11.93/2.00      ( ~ r3_lattice3(X0_47,X0_45,X0_48)
% 11.93/2.00      | r3_lattice3(X0_47,X1_45,X0_48)
% 11.93/2.00      | X1_45 != X0_45 ),
% 11.93/2.00      theory(equality) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1709,plain,
% 11.93/2.00      ( ~ r3_lattice3(sK3,X0_45,X0_48)
% 11.93/2.00      | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),X0_48)
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,sK4)) != X0_45 ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_648]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1710,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK4)) != X0_45
% 11.93/2.00      | r3_lattice3(sK3,X0_45,X0_48) != iProver_top
% 11.93/2.00      | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),X0_48) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1709]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1712,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK4)) != sK4
% 11.93/2.00      | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),sK2) = iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) != iProver_top ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_1710]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_649,plain,
% 11.93/2.00      ( ~ r2_hidden(X0_45,X0_48)
% 11.93/2.00      | r2_hidden(X1_45,X0_48)
% 11.93/2.00      | X1_45 != X0_45 ),
% 11.93/2.00      theory(equality) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_2004,plain,
% 11.93/2.00      ( r2_hidden(X0_45,sK2)
% 11.93/2.00      | ~ r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2)
% 11.93/2.00      | X0_45 != sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_649]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3154,plain,
% 11.93/2.00      ( ~ r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2)
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2)
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) != sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_2004]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3156,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) != sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)
% 11.93/2.00      | r2_hidden(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),sK2) != iProver_top
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_3154]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3155,plain,
% 11.93/2.00      ( ~ m1_subset_1(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),u1_struct_0(sK3))
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) = sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_639]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3158,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) = sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)
% 11.93/2.00      | m1_subset_1(sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_3155]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_645,plain,
% 11.93/2.00      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 11.93/2.00      theory(equality) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1224,plain,
% 11.93/2.00      ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != X0_45
% 11.93/2.00      | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,X1_45)
% 11.93/2.00      | k7_lattices(sK3,X1_45) != X0_45 ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_645]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1841,plain,
% 11.93/2.00      ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,X0_45)
% 11.93/2.00      | k7_lattices(sK3,X0_45) != sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_1224]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3561,plain,
% 11.93/2.00      ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) != sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_1841]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_646,plain,
% 11.93/2.00      ( X0_45 != X1_45
% 11.93/2.00      | k7_lattices(X0_47,X0_45) = k7_lattices(X0_47,X1_45) ),
% 11.93/2.00      theory(equality) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_2513,plain,
% 11.93/2.00      ( X0_45 != X1_45
% 11.93/2.00      | k7_lattices(sK3,X0_45) = k7_lattices(sK3,X1_45) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_646]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3594,plain,
% 11.93/2.00      ( X0_45 != sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)
% 11.93/2.00      | k7_lattices(sK3,X0_45) = k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_2513]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_6764,plain,
% 11.93/2.00      ( k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)) != sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) = k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_3594]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_5256,plain,
% 11.93/2.00      ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,X0_45)
% 11.93/2.00      | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | k7_lattices(sK3,X0_45) != k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_1224]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_13641,plain,
% 11.93/2.00      ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)))
% 11.93/2.00      | k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) != k7_lattices(sK3,sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_5256]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3932,plain,
% 11.93/2.00      ( r2_hidden(X0_45,sK2)
% 11.93/2.00      | ~ r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2)
% 11.93/2.00      | X0_45 != k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_649]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_34130,plain,
% 11.93/2.00      ( r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),sK2)
% 11.93/2.00      | ~ r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2)
% 11.93/2.00      | sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_3932]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_34131,plain,
% 11.93/2.00      ( sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3)))
% 11.93/2.00      | r2_hidden(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),sK2) = iProver_top
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,k7_lattices(sK3,sK1(sK1(sK0(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)),a_2_0_lattice3(sK2,sK3),sK3),sK2,sK3))),sK2) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_34130]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_36474,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,sK2) != iProver_top ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_12420,c_14,c_23,c_301,c_660,c_683,c_1084,c_1090,
% 11.93/2.00                 c_1132,c_1134,c_1138,c_1384,c_1632,c_1634,c_1636,c_1712,
% 11.93/2.00                 c_3156,c_3158,c_3561,c_6764,c_13641,c_34131]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_36483,plain,
% 11.93/2.00      ( k7_lattices(sK3,k7_lattices(sK3,sK0(sK3,sK4,sK2))) = sK0(sK3,sK4,sK2) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_2635,c_36474]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_36545,plain,
% 11.93/2.00      ( r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(X0_48,sK3)) = iProver_top
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,sK0(sK3,sK4,sK2)),X0_48) != iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,sK0(sK3,sK4,sK2)),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_36483,c_983]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_675,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top
% 11.93/2.00      | m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3)) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_677,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,sK2) = iProver_top
% 11.93/2.00      | m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) = iProver_top
% 11.93/2.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_675]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1431,plain,
% 11.93/2.00      ( ~ m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3))
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,sK0(sK3,X0_45,X0_48)),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_631]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1432,plain,
% 11.93/2.00      ( m1_subset_1(sK0(sK3,X0_45,X0_48),u1_struct_0(sK3)) != iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,sK0(sK3,X0_45,X0_48)),u1_struct_0(sK3)) = iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1431]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1434,plain,
% 11.93/2.00      ( m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) != iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,sK0(sK3,sK4,sK2)),u1_struct_0(sK3)) = iProver_top ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_1432]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_37389,plain,
% 11.93/2.00      ( r2_hidden(k7_lattices(sK3,sK0(sK3,sK4,sK2)),X0_48) != iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(X0_48,sK3)) = iProver_top ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_36545,c_14,c_23,c_301,c_660,c_677,c_683,c_1084,c_1090,
% 11.93/2.00                 c_1132,c_1134,c_1138,c_1384,c_1434,c_1632,c_1634,c_1636,
% 11.93/2.00                 c_1712,c_3156,c_3158,c_3561,c_6764,c_13641,c_34131]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_37390,plain,
% 11.93/2.00      ( r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(X0_48,sK3)) = iProver_top
% 11.93/2.00      | r2_hidden(k7_lattices(sK3,sK0(sK3,sK4,sK2)),X0_48) != iProver_top ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_37389]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_37397,plain,
% 11.93/2.00      ( r2_hidden(sK0(sK3,sK4,sK2),X0_48) != iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(a_2_0_lattice3(X0_48,sK3),sK3)) = iProver_top
% 11.93/2.00      | m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_983,c_37390]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_37399,plain,
% 11.93/2.00      ( r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,sK4,sK2),sK2) != iProver_top
% 11.93/2.00      | m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_37397]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_11,plain,
% 11.93/2.00      ( ~ r4_lattice3(X0,X1,X2)
% 11.93/2.00      | r3_lattice3(X0,k7_lattices(X0,X1),a_2_0_lattice3(X2,X0))
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | ~ v10_lattices(X0)
% 11.93/2.00      | ~ v17_lattices(X0)
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0) ),
% 11.93/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_13,negated_conjecture,
% 11.93/2.00      ( r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) ),
% 11.93/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_142,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3)) ),
% 11.93/2.00      inference(prop_impl,[status(thm)],[c_13]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_143,plain,
% 11.93/2.00      ( r4_lattice3(sK3,k7_lattices(sK3,sK4),a_2_0_lattice3(sK2,sK3))
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_142]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_313,plain,
% 11.93/2.00      ( r3_lattice3(X0,k7_lattices(X0,X1),a_2_0_lattice3(X2,X0))
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.93/2.00      | ~ v10_lattices(X0)
% 11.93/2.00      | ~ v17_lattices(X0)
% 11.93/2.00      | v2_struct_0(X0)
% 11.93/2.00      | ~ l3_lattices(X0)
% 11.93/2.00      | a_2_0_lattice3(sK2,sK3) != X2
% 11.93/2.00      | k7_lattices(sK3,sK4) != X1
% 11.93/2.00      | sK3 != X0 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_11,c_143]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_314,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3))
% 11.93/2.00      | ~ v10_lattices(sK3)
% 11.93/2.00      | ~ v17_lattices(sK3)
% 11.93/2.00      | v2_struct_0(sK3)
% 11.93/2.00      | ~ l3_lattices(sK3) ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_313]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_316,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_314,c_18,c_17,c_16,c_15]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_640,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2)
% 11.93/2.00      | ~ m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) ),
% 11.93/2.00      inference(subtyping,[status(esa)],[c_316]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_978,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) = iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_318,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) = iProver_top
% 11.93/2.00      | m1_subset_1(k7_lattices(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1349,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,sK2) = iProver_top
% 11.93/2.00      | r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top ),
% 11.93/2.00      inference(global_propositional_subsumption,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_978,c_23,c_318,c_683]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1350,plain,
% 11.93/2.00      ( r3_lattice3(sK3,k7_lattices(sK3,k7_lattices(sK3,sK4)),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) = iProver_top ),
% 11.93/2.00      inference(renaming,[status(thm)],[c_1349]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1353,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) = iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) = iProver_top ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_1350,c_1080]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1264,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0_45,X0_48)
% 11.93/2.00      | ~ r3_lattice3(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | ~ r2_hidden(sK0(sK3,X0_45,X0_48),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3))
% 11.93/2.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK3)) ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_634]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1265,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
% 11.93/2.00      | r3_lattice3(sK3,X0_45,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,X0_45,X0_48),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1267,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
% 11.93/2.00      | r3_lattice3(sK3,sK4,sK2) = iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,sK4,sK2),a_2_0_lattice3(a_2_0_lattice3(sK2,sK3),sK3)) != iProver_top
% 11.93/2.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_1265]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_678,plain,
% 11.93/2.00      ( r3_lattice3(sK3,X0_45,X0_48) = iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,X0_45,X0_48),X0_48) = iProver_top
% 11.93/2.00      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_680,plain,
% 11.93/2.00      ( r3_lattice3(sK3,sK4,sK2) = iProver_top
% 11.93/2.00      | r2_hidden(sK0(sK3,sK4,sK2),sK2) = iProver_top
% 11.93/2.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 11.93/2.00      inference(instantiation,[status(thm)],[c_678]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(contradiction,plain,
% 11.93/2.00      ( $false ),
% 11.93/2.00      inference(minisat,
% 11.93/2.00                [status(thm)],
% 11.93/2.00                [c_37399,c_36474,c_1353,c_1267,c_680,c_677,c_23]) ).
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  ------                               Statistics
% 11.93/2.00  
% 11.93/2.00  ------ General
% 11.93/2.00  
% 11.93/2.00  abstr_ref_over_cycles:                  0
% 11.93/2.00  abstr_ref_under_cycles:                 0
% 11.93/2.00  gc_basic_clause_elim:                   0
% 11.93/2.00  forced_gc_time:                         0
% 11.93/2.00  parsing_time:                           0.008
% 11.93/2.00  unif_index_cands_time:                  0.
% 11.93/2.00  unif_index_add_time:                    0.
% 11.93/2.00  orderings_time:                         0.
% 11.93/2.00  out_proof_time:                         0.016
% 11.93/2.00  total_time:                             1.398
% 11.93/2.00  num_of_symbols:                         49
% 11.93/2.00  num_of_terms:                           20342
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing
% 11.93/2.00  
% 11.93/2.00  num_of_splits:                          0
% 11.93/2.00  num_of_split_atoms:                     0
% 11.93/2.00  num_of_reused_defs:                     0
% 11.93/2.00  num_eq_ax_congr_red:                    26
% 11.93/2.00  num_of_sem_filtered_clauses:            1
% 11.93/2.00  num_of_subtypes:                        4
% 11.93/2.00  monotx_restored_types:                  0
% 11.93/2.00  sat_num_of_epr_types:                   0
% 11.93/2.00  sat_num_of_non_cyclic_types:            0
% 11.93/2.00  sat_guarded_non_collapsed_types:        1
% 11.93/2.00  num_pure_diseq_elim:                    0
% 11.93/2.00  simp_replaced_by:                       0
% 11.93/2.00  res_preprocessed:                       68
% 11.93/2.00  prep_upred:                             0
% 11.93/2.00  prep_unflattend:                        18
% 11.93/2.00  smt_new_axioms:                         0
% 11.93/2.00  pred_elim_cands:                        3
% 11.93/2.00  pred_elim:                              6
% 11.93/2.00  pred_elim_cl:                           7
% 11.93/2.00  pred_elim_cycles:                       8
% 11.93/2.00  merged_defs:                            6
% 11.93/2.00  merged_defs_ncl:                        0
% 11.93/2.00  bin_hyper_res:                          6
% 11.93/2.00  prep_cycles:                            4
% 11.93/2.00  pred_elim_time:                         0.006
% 11.93/2.00  splitting_time:                         0.
% 11.93/2.00  sem_filter_time:                        0.
% 11.93/2.00  monotx_time:                            0.
% 11.93/2.00  subtype_inf_time:                       0.
% 11.93/2.00  
% 11.93/2.00  ------ Problem properties
% 11.93/2.00  
% 11.93/2.00  clauses:                                12
% 11.93/2.00  conjectures:                            1
% 11.93/2.00  epr:                                    0
% 11.93/2.00  horn:                                   9
% 11.93/2.00  ground:                                 3
% 11.93/2.00  unary:                                  1
% 11.93/2.00  binary:                                 5
% 11.93/2.00  lits:                                   30
% 11.93/2.00  lits_eq:                                2
% 11.93/2.00  fd_pure:                                0
% 11.93/2.00  fd_pseudo:                              0
% 11.93/2.00  fd_cond:                                0
% 11.93/2.00  fd_pseudo_cond:                         0
% 11.93/2.00  ac_symbols:                             0
% 11.93/2.00  
% 11.93/2.00  ------ Propositional Solver
% 11.93/2.00  
% 11.93/2.00  prop_solver_calls:                      33
% 11.93/2.00  prop_fast_solver_calls:                 1221
% 11.93/2.00  smt_solver_calls:                       0
% 11.93/2.00  smt_fast_solver_calls:                  0
% 11.93/2.00  prop_num_of_clauses:                    13693
% 11.93/2.00  prop_preprocess_simplified:             13268
% 11.93/2.00  prop_fo_subsumed:                       45
% 11.93/2.00  prop_solver_time:                       0.
% 11.93/2.00  smt_solver_time:                        0.
% 11.93/2.00  smt_fast_solver_time:                   0.
% 11.93/2.00  prop_fast_solver_time:                  0.
% 11.93/2.00  prop_unsat_core_time:                   0.
% 11.93/2.00  
% 11.93/2.00  ------ QBF
% 11.93/2.00  
% 11.93/2.00  qbf_q_res:                              0
% 11.93/2.00  qbf_num_tautologies:                    0
% 11.93/2.00  qbf_prep_cycles:                        0
% 11.93/2.00  
% 11.93/2.00  ------ BMC1
% 11.93/2.00  
% 11.93/2.00  bmc1_current_bound:                     -1
% 11.93/2.00  bmc1_last_solved_bound:                 -1
% 11.93/2.00  bmc1_unsat_core_size:                   -1
% 11.93/2.00  bmc1_unsat_core_parents_size:           -1
% 11.93/2.00  bmc1_merge_next_fun:                    0
% 11.93/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.93/2.00  
% 11.93/2.00  ------ Instantiation
% 11.93/2.00  
% 11.93/2.00  inst_num_of_clauses:                    2824
% 11.93/2.00  inst_num_in_passive:                    166
% 11.93/2.00  inst_num_in_active:                     1287
% 11.93/2.00  inst_num_in_unprocessed:                1371
% 11.93/2.00  inst_num_of_loops:                      1430
% 11.93/2.00  inst_num_of_learning_restarts:          0
% 11.93/2.00  inst_num_moves_active_passive:          137
% 11.93/2.00  inst_lit_activity:                      0
% 11.93/2.00  inst_lit_activity_moves:                0
% 11.93/2.00  inst_num_tautologies:                   0
% 11.93/2.00  inst_num_prop_implied:                  0
% 11.93/2.00  inst_num_existing_simplified:           0
% 11.93/2.00  inst_num_eq_res_simplified:             0
% 11.93/2.00  inst_num_child_elim:                    0
% 11.93/2.00  inst_num_of_dismatching_blockings:      3260
% 11.93/2.00  inst_num_of_non_proper_insts:           4025
% 11.93/2.00  inst_num_of_duplicates:                 0
% 11.93/2.00  inst_inst_num_from_inst_to_res:         0
% 11.93/2.00  inst_dismatching_checking_time:         0.
% 11.93/2.00  
% 11.93/2.00  ------ Resolution
% 11.93/2.00  
% 11.93/2.00  res_num_of_clauses:                     0
% 11.93/2.00  res_num_in_passive:                     0
% 11.93/2.00  res_num_in_active:                      0
% 11.93/2.00  res_num_of_loops:                       72
% 11.93/2.00  res_forward_subset_subsumed:            58
% 11.93/2.00  res_backward_subset_subsumed:           0
% 11.93/2.00  res_forward_subsumed:                   0
% 11.93/2.00  res_backward_subsumed:                  0
% 11.93/2.00  res_forward_subsumption_resolution:     1
% 11.93/2.00  res_backward_subsumption_resolution:    0
% 11.93/2.00  res_clause_to_clause_subsumption:       14721
% 11.93/2.00  res_orphan_elimination:                 0
% 11.93/2.00  res_tautology_del:                      813
% 11.93/2.00  res_num_eq_res_simplified:              0
% 11.93/2.00  res_num_sel_changes:                    0
% 11.93/2.00  res_moves_from_active_to_pass:          0
% 11.93/2.00  
% 11.93/2.00  ------ Superposition
% 11.93/2.00  
% 11.93/2.00  sup_time_total:                         0.
% 11.93/2.00  sup_time_generating:                    0.
% 11.93/2.00  sup_time_sim_full:                      0.
% 11.93/2.00  sup_time_sim_immed:                     0.
% 11.93/2.00  
% 11.93/2.00  sup_num_of_clauses:                     1563
% 11.93/2.00  sup_num_in_active:                      250
% 11.93/2.00  sup_num_in_passive:                     1313
% 11.93/2.00  sup_num_of_loops:                       285
% 11.93/2.00  sup_fw_superposition:                   1169
% 11.93/2.00  sup_bw_superposition:                   740
% 11.93/2.00  sup_immediate_simplified:               133
% 11.93/2.00  sup_given_eliminated:                   0
% 11.93/2.00  comparisons_done:                       0
% 11.93/2.00  comparisons_avoided:                    114
% 11.93/2.00  
% 11.93/2.00  ------ Simplifications
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  sim_fw_subset_subsumed:                 35
% 11.93/2.00  sim_bw_subset_subsumed:                 145
% 11.93/2.00  sim_fw_subsumed:                        21
% 11.93/2.00  sim_bw_subsumed:                        0
% 11.93/2.00  sim_fw_subsumption_res:                 1
% 11.93/2.00  sim_bw_subsumption_res:                 0
% 11.93/2.00  sim_tautology_del:                      2
% 11.93/2.00  sim_eq_tautology_del:                   29
% 11.93/2.00  sim_eq_res_simp:                        0
% 11.93/2.00  sim_fw_demodulated:                     0
% 11.93/2.00  sim_bw_demodulated:                     31
% 11.93/2.00  sim_light_normalised:                   100
% 11.93/2.00  sim_joinable_taut:                      0
% 11.93/2.00  sim_joinable_simp:                      0
% 11.93/2.00  sim_ac_normalised:                      0
% 11.93/2.00  sim_smt_subsumption:                    0
% 11.93/2.00  
%------------------------------------------------------------------------------

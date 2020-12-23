%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:10 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 701 expanded)
%              Number of clauses        :  116 ( 180 expanded)
%              Number of leaves         :   20 ( 203 expanded)
%              Depth                    :   21
%              Number of atoms          :  986 (4646 expanded)
%              Number of equality atoms :   72 ( 114 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r2_hidden(X1,X2)
               => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                  & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
            | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
          & r2_hidden(X1,X2) )
     => ( ( ~ r3_lattices(X0,k16_lattice3(X0,sK6),X1)
          | ~ r3_lattices(X0,X1,k15_lattice3(X0,sK6)) )
        & r2_hidden(X1,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),sK5)
              | ~ r3_lattices(X0,sK5,k15_lattice3(X0,X2)) )
            & r2_hidden(sK5,X2) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                  | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,X2),X1)
                | ~ r3_lattices(sK4,X1,k15_lattice3(sK4,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
      | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) )
    & r2_hidden(sK5,sK6)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f52,f51,f50])).

fof(f79,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f57,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

fof(f59,plain,(
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

fof(f55,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f81,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f85,plain,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2997,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_2996,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_4099,plain,
    ( X0_53 != X1_53
    | X1_53 = X0_53 ),
    inference(resolution,[status(thm)],[c_2997,c_2996])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_888,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | sK3(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_889,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ l3_lattices(sK4)
    | sK3(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_28,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_893,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | sK3(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_889,c_28])).

cnf(c_2972,plain,
    ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
    | sK3(X0_53,sK4,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_893])).

cnf(c_5188,plain,
    ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
    | X0_53 = sK3(X0_53,sK4,X0_54) ),
    inference(resolution,[status(thm)],[c_4099,c_2972])).

cnf(c_3001,plain,
    ( ~ r3_lattice3(X0_52,X0_53,X0_54)
    | r3_lattice3(X0_52,X1_53,X0_54)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_5372,plain,
    ( r3_lattice3(X0_52,X0_53,X0_54)
    | ~ r3_lattice3(X0_52,sK3(X0_53,sK4,X1_54),X0_54)
    | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X1_54)) ),
    inference(resolution,[status(thm)],[c_5188,c_3001])).

cnf(c_22,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_625,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_626,plain,
    ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_630,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | r3_lattice3(sK4,sK3(X0,sK4,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_28])).

cnf(c_631,plain,
    ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_630])).

cnf(c_2985,plain,
    ( r3_lattice3(sK4,sK3(X0_53,sK4,X0_54),X0_54)
    | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) ),
    inference(subtyping,[status(esa)],[c_631])).

cnf(c_12198,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) ),
    inference(resolution,[status(thm)],[c_5372,c_2985])).

cnf(c_11,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_738,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_739,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_28])).

cnf(c_744,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_743])).

cnf(c_2979,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_744])).

cnf(c_12297,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r3_lattice3(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_12198,c_2979])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_780,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_781,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_785,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_28])).

cnf(c_786,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_785])).

cnf(c_2977,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X0_53,X1_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_786])).

cnf(c_12331,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r1_lattices(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X1_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_12297,c_2977])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_717,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_718,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_722,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_28])).

cnf(c_723,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_722])).

cnf(c_2980,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_723])).

cnf(c_8293,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2980])).

cnf(c_13063,plain,
    ( ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ r2_hidden(X1_53,X0_54)
    | r1_lattices(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X1_53)
    | r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12331,c_8293])).

cnf(c_13064,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r1_lattices(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X1_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_13063])).

cnf(c_10,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_759,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_760,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_28])).

cnf(c_765,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_764])).

cnf(c_2978,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_765])).

cnf(c_13097,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_13064,c_2978])).

cnf(c_13099,plain,
    ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_13097])).

cnf(c_2999,plain,
    ( ~ r1_lattices(X0_52,X0_53,X1_53)
    | r1_lattices(X0_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_6379,plain,
    ( ~ r1_lattices(X0_52,X0_53,X1_53)
    | r1_lattices(X0_52,X2_53,X1_53)
    | X2_53 != X0_53 ),
    inference(resolution,[status(thm)],[c_2999,c_2996])).

cnf(c_19,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_679,plain,
    ( ~ l3_lattices(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_680,plain,
    ( ~ l3_lattices(sK4)
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_684,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_28])).

cnf(c_2982,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) = k16_lattice3(sK4,X0_54) ),
    inference(subtyping,[status(esa)],[c_684])).

cnf(c_5192,plain,
    ( k16_lattice3(sK4,X0_54) = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
    inference(resolution,[status(thm)],[c_4099,c_2982])).

cnf(c_6418,plain,
    ( r1_lattices(X0_52,k16_lattice3(sK4,X0_54),X0_53)
    | ~ r1_lattices(X0_52,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X0_53) ),
    inference(resolution,[status(thm)],[c_6379,c_5192])).

cnf(c_6420,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK5) ),
    inference(instantiation,[status(thm)],[c_6418])).

cnf(c_20,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_664,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_665,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_669,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_28])).

cnf(c_2983,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_669])).

cnf(c_3501,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2983])).

cnf(c_3832,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_3501])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_386,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_4])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_390,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_2,c_1])).

cnf(c_30,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_567,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_390,c_30])).

cnf(c_568,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_572,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_31,c_28])).

cnf(c_573,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_572])).

cnf(c_2987,plain,
    ( ~ r1_lattices(sK4,X0_53,X1_53)
    | r3_lattices(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_573])).

cnf(c_3497,plain,
    ( r1_lattices(sK4,X0_53,X1_53) != iProver_top
    | r3_lattices(sK4,X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2987])).

cnf(c_4317,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) != iProver_top
    | r3_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3832,c_3497])).

cnf(c_4366,plain,
    ( ~ r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53)
    | r3_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4317])).

cnf(c_4368,plain,
    ( ~ r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4366])).

cnf(c_4023,plain,
    ( ~ r1_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54))
    | r3_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2987])).

cnf(c_4025,plain,
    ( ~ r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4023])).

cnf(c_17,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_29,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_449,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_450,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_454,plain,
    ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_31,c_30,c_28])).

cnf(c_455,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_914,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_669,c_455])).

cnf(c_2971,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_914])).

cnf(c_3943,plain,
    ( ~ r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2971])).

cnf(c_3960,plain,
    ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3943])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_690,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_691,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_28])).

cnf(c_696,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_695])).

cnf(c_2981,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X1_53,X0_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_696])).

cnf(c_3794,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54)
    | r1_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54))
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2981])).

cnf(c_3796,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6)
    | r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,sK6)
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3794])).

cnf(c_3040,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2983])).

cnf(c_18,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_190,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_20])).

cnf(c_434,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_29])).

cnf(c_435,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_439,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_31,c_30,c_28])).

cnf(c_2991,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_439])).

cnf(c_3016,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2991])).

cnf(c_25,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13099,c_6420,c_4368,c_4025,c_3960,c_3796,c_3040,c_3016,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.32  % Computer   : n016.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 11:38:49 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.32  % Running in FOF mode
% 3.36/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/0.96  
% 3.36/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/0.96  
% 3.36/0.96  ------  iProver source info
% 3.36/0.96  
% 3.36/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.36/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/0.96  git: non_committed_changes: false
% 3.36/0.96  git: last_make_outside_of_git: false
% 3.36/0.96  
% 3.36/0.96  ------ 
% 3.36/0.96  ------ Parsing...
% 3.36/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/0.96  
% 3.36/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.36/0.96  
% 3.36/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/0.96  
% 3.36/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/0.96  ------ Proving...
% 3.36/0.96  ------ Problem Properties 
% 3.36/0.96  
% 3.36/0.96  
% 3.36/0.96  clauses                                 24
% 3.36/0.96  conjectures                             3
% 3.36/0.96  EPR                                     1
% 3.36/0.96  Horn                                    18
% 3.36/0.96  unary                                   5
% 3.36/0.96  binary                                  4
% 3.36/0.96  lits                                    67
% 3.36/0.96  lits eq                                 5
% 3.36/0.96  fd_pure                                 0
% 3.36/0.96  fd_pseudo                               0
% 3.36/0.96  fd_cond                                 0
% 3.36/0.96  fd_pseudo_cond                          3
% 3.36/0.96  AC symbols                              0
% 3.36/0.96  
% 3.36/0.96  ------ Input Options Time Limit: Unbounded
% 3.36/0.96  
% 3.36/0.96  
% 3.36/0.96  ------ 
% 3.36/0.96  Current options:
% 3.36/0.96  ------ 
% 3.36/0.96  
% 3.36/0.96  
% 3.36/0.96  
% 3.36/0.96  
% 3.36/0.96  ------ Proving...
% 3.36/0.96  
% 3.36/0.96  
% 3.36/0.96  % SZS status Theorem for theBenchmark.p
% 3.36/0.96  
% 3.36/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/0.96  
% 3.36/0.96  fof(f8,axiom,(
% 3.36/0.96    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f28,plain,(
% 3.36/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 3.36/0.96    inference(ennf_transformation,[],[f8])).
% 3.36/0.96  
% 3.36/0.96  fof(f29,plain,(
% 3.36/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.36/0.96    inference(flattening,[],[f28])).
% 3.36/0.96  
% 3.36/0.96  fof(f46,plain,(
% 3.36/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.36/0.96    inference(nnf_transformation,[],[f29])).
% 3.36/0.96  
% 3.36/0.96  fof(f47,plain,(
% 3.36/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.36/0.96    inference(rectify,[],[f46])).
% 3.36/0.96  
% 3.36/0.96  fof(f48,plain,(
% 3.36/0.96    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 3.36/0.96    introduced(choice_axiom,[])).
% 3.36/0.96  
% 3.36/0.96  fof(f49,plain,(
% 3.36/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.36/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 3.36/0.96  
% 3.36/0.96  fof(f76,plain,(
% 3.36/0.96    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f49])).
% 3.36/0.96  
% 3.36/0.96  fof(f9,conjecture,(
% 3.36/0.96    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f10,negated_conjecture,(
% 3.36/0.96    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 3.36/0.96    inference(negated_conjecture,[],[f9])).
% 3.36/0.96  
% 3.36/0.96  fof(f30,plain,(
% 3.36/0.96    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.36/0.96    inference(ennf_transformation,[],[f10])).
% 3.36/0.96  
% 3.36/0.96  fof(f31,plain,(
% 3.36/0.96    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.36/0.96    inference(flattening,[],[f30])).
% 3.36/0.96  
% 3.36/0.96  fof(f52,plain,(
% 3.36/0.96    ( ! [X0,X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK6),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,sK6))) & r2_hidden(X1,sK6))) )),
% 3.36/0.96    introduced(choice_axiom,[])).
% 3.36/0.96  
% 3.36/0.96  fof(f51,plain,(
% 3.36/0.96    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),sK5) | ~r3_lattices(X0,sK5,k15_lattice3(X0,X2))) & r2_hidden(sK5,X2)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.36/0.96    introduced(choice_axiom,[])).
% 3.36/0.96  
% 3.36/0.96  fof(f50,plain,(
% 3.36/0.96    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK4,k16_lattice3(sK4,X2),X1) | ~r3_lattices(sK4,X1,k15_lattice3(sK4,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 3.36/0.96    introduced(choice_axiom,[])).
% 3.36/0.96  
% 3.36/0.96  fof(f53,plain,(
% 3.36/0.96    (((~r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) | ~r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))) & r2_hidden(sK5,sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 3.36/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f52,f51,f50])).
% 3.36/0.96  
% 3.36/0.96  fof(f79,plain,(
% 3.36/0.96    ~v2_struct_0(sK4)),
% 3.36/0.96    inference(cnf_transformation,[],[f53])).
% 3.36/0.96  
% 3.36/0.96  fof(f82,plain,(
% 3.36/0.96    l3_lattices(sK4)),
% 3.36/0.96    inference(cnf_transformation,[],[f53])).
% 3.36/0.96  
% 3.36/0.96  fof(f77,plain,(
% 3.36/0.96    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK3(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f49])).
% 3.36/0.96  
% 3.36/0.96  fof(f4,axiom,(
% 3.36/0.96    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f20,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.36/0.96    inference(ennf_transformation,[],[f4])).
% 3.36/0.96  
% 3.36/0.96  fof(f21,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(flattening,[],[f20])).
% 3.36/0.96  
% 3.36/0.96  fof(f37,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(nnf_transformation,[],[f21])).
% 3.36/0.96  
% 3.36/0.96  fof(f38,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(rectify,[],[f37])).
% 3.36/0.96  
% 3.36/0.96  fof(f39,plain,(
% 3.36/0.96    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.36/0.96    introduced(choice_axiom,[])).
% 3.36/0.96  
% 3.36/0.96  fof(f40,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.36/0.96  
% 3.36/0.96  fof(f66,plain,(
% 3.36/0.96    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f40])).
% 3.36/0.96  
% 3.36/0.96  fof(f3,axiom,(
% 3.36/0.96    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f18,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.36/0.96    inference(ennf_transformation,[],[f3])).
% 3.36/0.96  
% 3.36/0.96  fof(f19,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(flattening,[],[f18])).
% 3.36/0.96  
% 3.36/0.96  fof(f33,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(nnf_transformation,[],[f19])).
% 3.36/0.96  
% 3.36/0.96  fof(f34,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(rectify,[],[f33])).
% 3.36/0.96  
% 3.36/0.96  fof(f35,plain,(
% 3.36/0.96    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.36/0.96    introduced(choice_axiom,[])).
% 3.36/0.96  
% 3.36/0.96  fof(f36,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.36/0.96  
% 3.36/0.96  fof(f60,plain,(
% 3.36/0.96    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f36])).
% 3.36/0.96  
% 3.36/0.96  fof(f65,plain,(
% 3.36/0.96    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f40])).
% 3.36/0.96  
% 3.36/0.96  fof(f67,plain,(
% 3.36/0.96    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f40])).
% 3.36/0.96  
% 3.36/0.96  fof(f6,axiom,(
% 3.36/0.96    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f24,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.36/0.96    inference(ennf_transformation,[],[f6])).
% 3.36/0.96  
% 3.36/0.96  fof(f25,plain,(
% 3.36/0.96    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(flattening,[],[f24])).
% 3.36/0.96  
% 3.36/0.96  fof(f73,plain,(
% 3.36/0.96    ( ! [X0,X1] : (k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f25])).
% 3.36/0.96  
% 3.36/0.96  fof(f7,axiom,(
% 3.36/0.96    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f26,plain,(
% 3.36/0.96    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.36/0.96    inference(ennf_transformation,[],[f7])).
% 3.36/0.96  
% 3.36/0.96  fof(f27,plain,(
% 3.36/0.96    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(flattening,[],[f26])).
% 3.36/0.96  
% 3.36/0.96  fof(f74,plain,(
% 3.36/0.96    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f27])).
% 3.36/0.96  
% 3.36/0.96  fof(f1,axiom,(
% 3.36/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f11,plain,(
% 3.36/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.36/0.96    inference(pure_predicate_removal,[],[f1])).
% 3.36/0.96  
% 3.36/0.96  fof(f12,plain,(
% 3.36/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.36/0.96    inference(pure_predicate_removal,[],[f11])).
% 3.36/0.96  
% 3.36/0.96  fof(f13,plain,(
% 3.36/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 3.36/0.96    inference(pure_predicate_removal,[],[f12])).
% 3.36/0.96  
% 3.36/0.96  fof(f14,plain,(
% 3.36/0.96    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.36/0.96    inference(ennf_transformation,[],[f13])).
% 3.36/0.96  
% 3.36/0.96  fof(f15,plain,(
% 3.36/0.96    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.36/0.96    inference(flattening,[],[f14])).
% 3.36/0.96  
% 3.36/0.96  fof(f57,plain,(
% 3.36/0.96    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f15])).
% 3.36/0.96  
% 3.36/0.96  fof(f2,axiom,(
% 3.36/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f16,plain,(
% 3.36/0.96    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.36/0.96    inference(ennf_transformation,[],[f2])).
% 3.36/0.96  
% 3.36/0.96  fof(f17,plain,(
% 3.36/0.96    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(flattening,[],[f16])).
% 3.36/0.96  
% 3.36/0.96  fof(f32,plain,(
% 3.36/0.96    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(nnf_transformation,[],[f17])).
% 3.36/0.96  
% 3.36/0.96  fof(f59,plain,(
% 3.36/0.96    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f32])).
% 3.36/0.96  
% 3.36/0.96  fof(f55,plain,(
% 3.36/0.96    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f15])).
% 3.36/0.96  
% 3.36/0.96  fof(f56,plain,(
% 3.36/0.96    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f15])).
% 3.36/0.96  
% 3.36/0.96  fof(f80,plain,(
% 3.36/0.96    v10_lattices(sK4)),
% 3.36/0.96    inference(cnf_transformation,[],[f53])).
% 3.36/0.96  
% 3.36/0.96  fof(f5,axiom,(
% 3.36/0.96    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 3.36/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.96  
% 3.36/0.96  fof(f22,plain,(
% 3.36/0.96    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.36/0.96    inference(ennf_transformation,[],[f5])).
% 3.36/0.96  
% 3.36/0.96  fof(f23,plain,(
% 3.36/0.96    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(flattening,[],[f22])).
% 3.36/0.96  
% 3.36/0.96  fof(f41,plain,(
% 3.36/0.96    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(nnf_transformation,[],[f23])).
% 3.36/0.96  
% 3.36/0.96  fof(f42,plain,(
% 3.36/0.96    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(flattening,[],[f41])).
% 3.36/0.96  
% 3.36/0.96  fof(f43,plain,(
% 3.36/0.96    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(rectify,[],[f42])).
% 3.36/0.96  
% 3.36/0.96  fof(f44,plain,(
% 3.36/0.96    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.36/0.96    introduced(choice_axiom,[])).
% 3.36/0.96  
% 3.36/0.96  fof(f45,plain,(
% 3.36/0.96    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.36/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 3.36/0.96  
% 3.36/0.96  fof(f69,plain,(
% 3.36/0.96    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f45])).
% 3.36/0.96  
% 3.36/0.96  fof(f86,plain,(
% 3.36/0.96    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(equality_resolution,[],[f69])).
% 3.36/0.96  
% 3.36/0.96  fof(f81,plain,(
% 3.36/0.96    v4_lattice3(sK4)),
% 3.36/0.96    inference(cnf_transformation,[],[f53])).
% 3.36/0.96  
% 3.36/0.96  fof(f64,plain,(
% 3.36/0.96    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f40])).
% 3.36/0.96  
% 3.36/0.96  fof(f68,plain,(
% 3.36/0.96    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(cnf_transformation,[],[f45])).
% 3.36/0.96  
% 3.36/0.96  fof(f87,plain,(
% 3.36/0.96    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.36/0.96    inference(equality_resolution,[],[f68])).
% 3.36/0.96  
% 3.36/0.96  fof(f85,plain,(
% 3.36/0.96    ~r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) | ~r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))),
% 3.36/0.96    inference(cnf_transformation,[],[f53])).
% 3.36/0.96  
% 3.36/0.96  fof(f84,plain,(
% 3.36/0.96    r2_hidden(sK5,sK6)),
% 3.36/0.96    inference(cnf_transformation,[],[f53])).
% 3.36/0.96  
% 3.36/0.96  fof(f83,plain,(
% 3.36/0.96    m1_subset_1(sK5,u1_struct_0(sK4))),
% 3.36/0.96    inference(cnf_transformation,[],[f53])).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2997,plain,
% 3.36/0.96      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 3.36/0.96      theory(equality) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2996,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_4099,plain,
% 3.36/0.96      ( X0_53 != X1_53 | X1_53 = X0_53 ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_2997,c_2996]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_23,plain,
% 3.36/0.96      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.36/0.96      | ~ l3_lattices(X1)
% 3.36/0.96      | v2_struct_0(X1)
% 3.36/0.96      | sK3(X0,X1,X2) = X0 ),
% 3.36/0.96      inference(cnf_transformation,[],[f76]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_31,negated_conjecture,
% 3.36/0.96      ( ~ v2_struct_0(sK4) ),
% 3.36/0.96      inference(cnf_transformation,[],[f79]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_888,plain,
% 3.36/0.96      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.36/0.96      | ~ l3_lattices(X1)
% 3.36/0.96      | sK3(X0,X1,X2) = X0
% 3.36/0.96      | sK4 != X1 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_889,plain,
% 3.36/0.96      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.36/0.96      | ~ l3_lattices(sK4)
% 3.36/0.96      | sK3(X0,sK4,X1) = X0 ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_888]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_28,negated_conjecture,
% 3.36/0.96      ( l3_lattices(sK4) ),
% 3.36/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_893,plain,
% 3.36/0.96      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) | sK3(X0,sK4,X1) = X0 ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_889,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2972,plain,
% 3.36/0.96      ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
% 3.36/0.96      | sK3(X0_53,sK4,X0_54) = X0_53 ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_893]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_5188,plain,
% 3.36/0.96      ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
% 3.36/0.96      | X0_53 = sK3(X0_53,sK4,X0_54) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_4099,c_2972]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3001,plain,
% 3.36/0.96      ( ~ r3_lattice3(X0_52,X0_53,X0_54)
% 3.36/0.96      | r3_lattice3(X0_52,X1_53,X0_54)
% 3.36/0.96      | X1_53 != X0_53 ),
% 3.36/0.96      theory(equality) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_5372,plain,
% 3.36/0.96      ( r3_lattice3(X0_52,X0_53,X0_54)
% 3.36/0.96      | ~ r3_lattice3(X0_52,sK3(X0_53,sK4,X1_54),X0_54)
% 3.36/0.96      | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X1_54)) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_5188,c_3001]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_22,plain,
% 3.36/0.96      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 3.36/0.96      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_625,plain,
% 3.36/0.96      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 3.36/0.96      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_626,plain,
% 3.36/0.96      ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
% 3.36/0.96      | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.36/0.96      | ~ l3_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_625]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_630,plain,
% 3.36/0.96      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.36/0.96      | r3_lattice3(sK4,sK3(X0,sK4,X1),X1) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_626,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_631,plain,
% 3.36/0.96      ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
% 3.36/0.96      | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_630]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2985,plain,
% 3.36/0.96      ( r3_lattice3(sK4,sK3(X0_53,sK4,X0_54),X0_54)
% 3.36/0.96      | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_631]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_12198,plain,
% 3.36/0.96      ( r3_lattice3(sK4,X0_53,X0_54)
% 3.36/0.96      | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_5372,c_2985]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_11,plain,
% 3.36/0.96      ( r4_lattice3(X0,X1,X2)
% 3.36/0.96      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_738,plain,
% 3.36/0.96      ( r4_lattice3(X0,X1,X2)
% 3.36/0.96      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_739,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ l3_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_738]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_743,plain,
% 3.36/0.96      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.36/0.96      | r4_lattice3(sK4,X0,X1) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_739,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_744,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_743]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2979,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0_53,X0_54)
% 3.36/0.96      | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_744]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_12297,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 3.36/0.96      | r3_lattice3(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_12198,c_2979]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_9,plain,
% 3.36/0.96      ( ~ r3_lattice3(X0,X1,X2)
% 3.36/0.96      | r1_lattices(X0,X1,X3)
% 3.36/0.96      | ~ r2_hidden(X3,X2)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_780,plain,
% 3.36/0.96      ( ~ r3_lattice3(X0,X1,X2)
% 3.36/0.96      | r1_lattices(X0,X1,X3)
% 3.36/0.96      | ~ r2_hidden(X3,X2)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_781,plain,
% 3.36/0.96      ( ~ r3_lattice3(sK4,X0,X1)
% 3.36/0.96      | r1_lattices(sK4,X0,X2)
% 3.36/0.96      | ~ r2_hidden(X2,X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.36/0.96      | ~ l3_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_780]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_785,plain,
% 3.36/0.96      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ r2_hidden(X2,X1)
% 3.36/0.96      | r1_lattices(sK4,X0,X2)
% 3.36/0.96      | ~ r3_lattice3(sK4,X0,X1) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_781,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_786,plain,
% 3.36/0.96      ( ~ r3_lattice3(sK4,X0,X1)
% 3.36/0.96      | r1_lattices(sK4,X0,X2)
% 3.36/0.96      | ~ r2_hidden(X2,X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_785]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2977,plain,
% 3.36/0.96      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 3.36/0.96      | r1_lattices(sK4,X0_53,X1_53)
% 3.36/0.96      | ~ r2_hidden(X1_53,X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_786]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_12331,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 3.36/0.96      | r1_lattices(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X1_53)
% 3.36/0.96      | ~ r2_hidden(X1_53,X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_12297,c_2977]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_12,plain,
% 3.36/0.96      ( r4_lattice3(X0,X1,X2)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f65]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_717,plain,
% 3.36/0.96      ( r4_lattice3(X0,X1,X2)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_718,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 3.36/0.96      | ~ l3_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_717]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_722,plain,
% 3.36/0.96      ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | r4_lattice3(sK4,X0,X1) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_718,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_723,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_722]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2980,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0_53,X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | m1_subset_1(sK1(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_723]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_8293,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | m1_subset_1(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_2980]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_13063,plain,
% 3.36/0.96      ( ~ m1_subset_1(X1_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ r2_hidden(X1_53,X0_54)
% 3.36/0.96      | r1_lattices(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X1_53)
% 3.36/0.96      | r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_12331,c_8293]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_13064,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 3.36/0.96      | r1_lattices(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X1_53)
% 3.36/0.96      | ~ r2_hidden(X1_53,X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_13063]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_10,plain,
% 3.36/0.96      ( r4_lattice3(X0,X1,X2)
% 3.36/0.96      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_759,plain,
% 3.36/0.96      ( r4_lattice3(X0,X1,X2)
% 3.36/0.96      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_10,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_760,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ l3_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_759]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_764,plain,
% 3.36/0.96      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.36/0.96      | r4_lattice3(sK4,X0,X1) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_760,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_765,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_764]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2978,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0_53,X0_54)
% 3.36/0.96      | ~ r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_765]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_13097,plain,
% 3.36/0.96      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 3.36/0.96      | ~ r2_hidden(X0_53,X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_13064,c_2978]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_13099,plain,
% 3.36/0.96      ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 3.36/0.96      | ~ r2_hidden(sK5,sK6)
% 3.36/0.96      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_13097]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2999,plain,
% 3.36/0.96      ( ~ r1_lattices(X0_52,X0_53,X1_53)
% 3.36/0.96      | r1_lattices(X0_52,X2_53,X3_53)
% 3.36/0.96      | X2_53 != X0_53
% 3.36/0.96      | X3_53 != X1_53 ),
% 3.36/0.96      theory(equality) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_6379,plain,
% 3.36/0.96      ( ~ r1_lattices(X0_52,X0_53,X1_53)
% 3.36/0.96      | r1_lattices(X0_52,X2_53,X1_53)
% 3.36/0.96      | X2_53 != X0_53 ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_2999,c_2996]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_19,plain,
% 3.36/0.96      ( ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
% 3.36/0.96      inference(cnf_transformation,[],[f73]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_679,plain,
% 3.36/0.96      ( ~ l3_lattices(X0)
% 3.36/0.96      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_680,plain,
% 3.36/0.96      ( ~ l3_lattices(sK4)
% 3.36/0.96      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_679]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_684,plain,
% 3.36/0.96      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_680,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2982,plain,
% 3.36/0.96      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) = k16_lattice3(sK4,X0_54) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_684]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_5192,plain,
% 3.36/0.96      ( k16_lattice3(sK4,X0_54) = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_4099,c_2982]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_6418,plain,
% 3.36/0.96      ( r1_lattices(X0_52,k16_lattice3(sK4,X0_54),X0_53)
% 3.36/0.96      | ~ r1_lattices(X0_52,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X0_53) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_6379,c_5192]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_6420,plain,
% 3.36/0.96      ( r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.36/0.96      | ~ r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK5) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_6418]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_20,plain,
% 3.36/0.96      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f74]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_664,plain,
% 3.36/0.96      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_665,plain,
% 3.36/0.96      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 3.36/0.96      | ~ l3_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_664]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_669,plain,
% 3.36/0.96      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_665,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2983,plain,
% 3.36/0.96      ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_669]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3501,plain,
% 3.36/0.96      ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 3.36/0.96      inference(predicate_to_equality,[status(thm)],[c_2983]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3832,plain,
% 3.36/0.96      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 3.36/0.96      inference(superposition,[status(thm)],[c_2982,c_3501]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_0,plain,
% 3.36/0.96      ( ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0)
% 3.36/0.96      | v9_lattices(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f57]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_4,plain,
% 3.36/0.96      ( ~ r1_lattices(X0,X1,X2)
% 3.36/0.96      | r3_lattices(X0,X1,X2)
% 3.36/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ v6_lattices(X0)
% 3.36/0.96      | ~ v8_lattices(X0)
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v9_lattices(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f59]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_386,plain,
% 3.36/0.96      ( ~ r1_lattices(X0,X1,X2)
% 3.36/0.96      | r3_lattices(X0,X1,X2)
% 3.36/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ v6_lattices(X0)
% 3.36/0.96      | ~ v8_lattices(X0)
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0) ),
% 3.36/0.96      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2,plain,
% 3.36/0.96      ( v6_lattices(X0)
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f55]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_1,plain,
% 3.36/0.96      ( v8_lattices(X0)
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_390,plain,
% 3.36/0.96      ( ~ r1_lattices(X0,X1,X2)
% 3.36/0.96      | r3_lattices(X0,X1,X2)
% 3.36/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_386,c_2,c_1]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_30,negated_conjecture,
% 3.36/0.96      ( v10_lattices(sK4) ),
% 3.36/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_567,plain,
% 3.36/0.96      ( ~ r1_lattices(X0,X1,X2)
% 3.36/0.96      | r3_lattices(X0,X1,X2)
% 3.36/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_390,c_30]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_568,plain,
% 3.36/0.96      ( ~ r1_lattices(sK4,X0,X1)
% 3.36/0.96      | r3_lattices(sK4,X0,X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.36/0.96      | ~ l3_lattices(sK4)
% 3.36/0.96      | v2_struct_0(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_567]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_572,plain,
% 3.36/0.96      ( ~ r1_lattices(sK4,X0,X1)
% 3.36/0.96      | r3_lattices(sK4,X0,X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_568,c_31,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_573,plain,
% 3.36/0.96      ( ~ r1_lattices(sK4,X0,X1)
% 3.36/0.96      | r3_lattices(sK4,X0,X1)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_572]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2987,plain,
% 3.36/0.96      ( ~ r1_lattices(sK4,X0_53,X1_53)
% 3.36/0.96      | r3_lattices(sK4,X0_53,X1_53)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_573]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3497,plain,
% 3.36/0.96      ( r1_lattices(sK4,X0_53,X1_53) != iProver_top
% 3.36/0.96      | r3_lattices(sK4,X0_53,X1_53) = iProver_top
% 3.36/0.96      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.36/0.96      | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
% 3.36/0.96      inference(predicate_to_equality,[status(thm)],[c_2987]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_4317,plain,
% 3.36/0.96      ( r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) != iProver_top
% 3.36/0.96      | r3_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
% 3.36/0.96      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.36/0.96      inference(superposition,[status(thm)],[c_3832,c_3497]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_4366,plain,
% 3.36/0.96      ( ~ r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53)
% 3.36/0.96      | r3_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_4317]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_4368,plain,
% 3.36/0.96      ( ~ r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.36/0.96      | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.36/0.96      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_4366]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_4023,plain,
% 3.36/0.96      ( ~ r1_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54))
% 3.36/0.96      | r3_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54))
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_2987]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_4025,plain,
% 3.36/0.96      ( ~ r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 3.36/0.96      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_4023]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_17,plain,
% 3.36/0.96      ( ~ r4_lattice3(X0,X1,X2)
% 3.36/0.96      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 3.36/0.96      | ~ v4_lattice3(X0)
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_29,negated_conjecture,
% 3.36/0.96      ( v4_lattice3(sK4) ),
% 3.36/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_449,plain,
% 3.36/0.96      ( ~ r4_lattice3(X0,X1,X2)
% 3.36/0.96      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_450,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 3.36/0.96      | ~ l3_lattices(sK4)
% 3.36/0.96      | v2_struct_0(sK4)
% 3.36/0.96      | ~ v10_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_449]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_454,plain,
% 3.36/0.96      ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 3.36/0.96      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_450,c_31,c_30,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_455,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_454]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_914,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(backward_subsumption_resolution,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_669,c_455]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2971,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 3.36/0.96      | r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_914]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3943,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 3.36/0.96      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X0_53)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_2971]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3960,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 3.36/0.96      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK5)
% 3.36/0.96      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_3943]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_13,plain,
% 3.36/0.96      ( ~ r4_lattice3(X0,X1,X2)
% 3.36/0.96      | r1_lattices(X0,X3,X1)
% 3.36/0.96      | ~ r2_hidden(X3,X2)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f64]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_690,plain,
% 3.36/0.96      ( ~ r4_lattice3(X0,X1,X2)
% 3.36/0.96      | r1_lattices(X0,X3,X1)
% 3.36/0.96      | ~ r2_hidden(X3,X2)
% 3.36/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.36/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_691,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | r1_lattices(sK4,X2,X0)
% 3.36/0.96      | ~ r2_hidden(X2,X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.36/0.96      | ~ l3_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_690]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_695,plain,
% 3.36/0.96      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ r2_hidden(X2,X1)
% 3.36/0.96      | r1_lattices(sK4,X2,X0)
% 3.36/0.96      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_691,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_696,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,X0,X1)
% 3.36/0.96      | r1_lattices(sK4,X2,X0)
% 3.36/0.96      | ~ r2_hidden(X2,X1)
% 3.36/0.96      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(renaming,[status(thm)],[c_695]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2981,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 3.36/0.96      | r1_lattices(sK4,X1_53,X0_53)
% 3.36/0.96      | ~ r2_hidden(X1_53,X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_696]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3794,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54)
% 3.36/0.96      | r1_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54))
% 3.36/0.96      | ~ r2_hidden(X0_53,X0_54)
% 3.36/0.96      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_2981]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3796,plain,
% 3.36/0.96      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6)
% 3.36/0.96      | r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 3.36/0.96      | ~ r2_hidden(sK5,sK6)
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
% 3.36/0.96      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_3794]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3040,plain,
% 3.36/0.96      ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_2983]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_18,plain,
% 3.36/0.96      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.36/0.96      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.36/0.96      | ~ v4_lattice3(X0)
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0) ),
% 3.36/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_190,plain,
% 3.36/0.96      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.36/0.96      | ~ v4_lattice3(X0)
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_18,c_20]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_434,plain,
% 3.36/0.96      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.36/0.96      | ~ l3_lattices(X0)
% 3.36/0.96      | v2_struct_0(X0)
% 3.36/0.96      | ~ v10_lattices(X0)
% 3.36/0.96      | sK4 != X0 ),
% 3.36/0.96      inference(resolution_lifted,[status(thm)],[c_190,c_29]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_435,plain,
% 3.36/0.96      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 3.36/0.96      | ~ l3_lattices(sK4)
% 3.36/0.96      | v2_struct_0(sK4)
% 3.36/0.96      | ~ v10_lattices(sK4) ),
% 3.36/0.96      inference(unflattening,[status(thm)],[c_434]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_439,plain,
% 3.36/0.96      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
% 3.36/0.96      inference(global_propositional_subsumption,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_435,c_31,c_30,c_28]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_2991,plain,
% 3.36/0.96      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54) ),
% 3.36/0.96      inference(subtyping,[status(esa)],[c_439]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_3016,plain,
% 3.36/0.96      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6) ),
% 3.36/0.96      inference(instantiation,[status(thm)],[c_2991]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_25,negated_conjecture,
% 3.36/0.96      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.36/0.96      | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
% 3.36/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_26,negated_conjecture,
% 3.36/0.96      ( r2_hidden(sK5,sK6) ),
% 3.36/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(c_27,negated_conjecture,
% 3.36/0.96      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.36/0.96      inference(cnf_transformation,[],[f83]) ).
% 3.36/0.96  
% 3.36/0.96  cnf(contradiction,plain,
% 3.36/0.96      ( $false ),
% 3.36/0.96      inference(minisat,
% 3.36/0.96                [status(thm)],
% 3.36/0.96                [c_13099,c_6420,c_4368,c_4025,c_3960,c_3796,c_3040,
% 3.36/0.96                 c_3016,c_25,c_26,c_27]) ).
% 3.36/0.96  
% 3.36/0.96  
% 3.36/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/0.96  
% 3.36/0.96  ------                               Statistics
% 3.36/0.96  
% 3.36/0.96  ------ Selected
% 3.36/0.96  
% 3.36/0.96  total_time:                             0.368
% 3.36/0.96  
%------------------------------------------------------------------------------

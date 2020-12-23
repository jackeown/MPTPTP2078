%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:09 EST 2020

% Result     : Theorem 31.51s
% Output     : CNFRefutation 31.51s
% Verified   : 
% Statistics : Number of formulae       :  266 (1297 expanded)
%              Number of clauses        :  179 ( 341 expanded)
%              Number of leaves         :   21 ( 334 expanded)
%              Depth                    :   31
%              Number of atoms          : 1305 (6385 expanded)
%              Number of equality atoms :  148 (1091 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
     => k15_lattice3(X0,sK7) != k16_lattice3(X0,a_2_2_lattice3(X0,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] : k15_lattice3(sK6,X1) != k16_lattice3(sK6,a_2_2_lattice3(sK6,X1))
      & l3_lattices(sK6)
      & v4_lattice3(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( k15_lattice3(sK6,sK7) != k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7))
    & l3_lattices(sK6)
    & v4_lattice3(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f28,f56,f55])).

fof(f89,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f57])).

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
    inference(ennf_transformation,[],[f1])).

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
    inference(flattening,[],[f11])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK5(X0,X1,X2),X1)
        & r3_lattice3(X0,sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK5(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK5(X0,X1,X2),X2)
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f52,f53])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f57])).

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
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK4(X0,X1,X2),X2)
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

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

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    k15_lattice3(sK6,sK7) != k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_854,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_29])).

cnf(c_855,plain,
    ( r4_lattice3(sK6,X0,X1)
    | r2_hidden(sK1(sK6,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_859,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(sK1(sK6,X0,X1),X1)
    | r4_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_855,c_32])).

cnf(c_860,plain,
    ( r4_lattice3(sK6,X0,X1)
    | r2_hidden(sK1(sK6,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_859])).

cnf(c_3004,plain,
    ( r4_lattice3(sK6,X0_51,X0_52)
    | r2_hidden(sK1(sK6,X0_51,X0_52),X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_860])).

cnf(c_3692,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | r2_hidden(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),X1_52)
    | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3004])).

cnf(c_87989,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7)
    | r2_hidden(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7),sK7)
    | ~ m1_subset_1(k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3692])).

cnf(c_3,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_896,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_29])).

cnf(c_897,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ r3_lattice3(sK6,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_901,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X1,X2)
    | ~ r3_lattice3(sK6,X0,X2)
    | r1_lattices(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_897,c_32])).

cnf(c_902,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ r3_lattice3(sK6,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_901])).

cnf(c_3002,plain,
    ( r1_lattices(sK6,X0_51,X1_51)
    | ~ r3_lattice3(sK6,X0_51,X0_52)
    | ~ r2_hidden(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_902])).

cnf(c_27,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_14,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_190,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_14])).

cnf(c_30,negated_conjecture,
    ( v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_436,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_30])).

cnf(c_437,plain,
    ( r3_lattice3(sK6,k16_lattice3(sK6,X0),X0)
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_31,negated_conjecture,
    ( v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_441,plain,
    ( r3_lattice3(sK6,k16_lattice3(sK6,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_32,c_31,c_29])).

cnf(c_3022,plain,
    ( r3_lattice3(sK6,k16_lattice3(sK6,X0_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_441])).

cnf(c_4748,plain,
    ( r1_lattices(sK6,k16_lattice3(sK6,X0_52),X0_51)
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_3002,c_3022])).

cnf(c_780,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_781,plain,
    ( m1_subset_1(k16_lattice3(sK6,X0),u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_785,plain,
    ( m1_subset_1(k16_lattice3(sK6,X0),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_32])).

cnf(c_3008,plain,
    ( m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_785])).

cnf(c_7697,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ r2_hidden(X0_51,X0_52)
    | r1_lattices(sK6,k16_lattice3(sK6,X0_52),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4748,c_3008])).

cnf(c_7698,plain,
    ( r1_lattices(sK6,k16_lattice3(sK6,X0_52),X0_51)
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_7697])).

cnf(c_8,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_628,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_629,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | ~ r1_lattices(sK6,X0,sK2(sK6,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6)
    | k15_lattice3(sK6,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_lattices(sK6,X0,sK2(sK6,X1,X0))
    | ~ r4_lattice3(sK6,X0,X1)
    | k15_lattice3(sK6,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_32,c_31,c_29])).

cnf(c_634,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | ~ r1_lattices(sK6,X0,sK2(sK6,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k15_lattice3(sK6,X1) = X0 ),
    inference(renaming,[status(thm)],[c_633])).

cnf(c_3013,plain,
    ( ~ r4_lattice3(sK6,X0_51,X0_52)
    | ~ r1_lattices(sK6,X0_51,sK2(sK6,X0_52,X0_51))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | k15_lattice3(sK6,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_634])).

cnf(c_7721,plain,
    ( ~ r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | ~ r2_hidden(sK2(sK6,X1_52,k16_lattice3(sK6,X0_52)),X0_52)
    | ~ m1_subset_1(sK2(sK6,X1_52,k16_lattice3(sK6,X0_52)),u1_struct_0(sK6))
    | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6))
    | k15_lattice3(sK6,X1_52) = k16_lattice3(sK6,X0_52) ),
    inference(resolution,[status(thm)],[c_7698,c_3013])).

cnf(c_10,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_580,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_581,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6)
    | k15_lattice3(sK6,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_585,plain,
    ( m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r4_lattice3(sK6,X0,X1)
    | k15_lattice3(sK6,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_581,c_32,c_31,c_29])).

cnf(c_586,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
    | k15_lattice3(sK6,X1) = X0 ),
    inference(renaming,[status(thm)],[c_585])).

cnf(c_3015,plain,
    ( ~ r4_lattice3(sK6,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X0_52,X0_51),u1_struct_0(sK6))
    | k15_lattice3(sK6,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_586])).

cnf(c_3803,plain,
    ( ~ r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | m1_subset_1(sK2(sK6,X1_52,k16_lattice3(sK6,X0_52)),u1_struct_0(sK6))
    | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6))
    | k15_lattice3(sK6,X1_52) = k16_lattice3(sK6,X0_52) ),
    inference(instantiation,[status(thm)],[c_3015])).

cnf(c_21884,plain,
    ( ~ r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | ~ r2_hidden(sK2(sK6,X1_52,k16_lattice3(sK6,X0_52)),X0_52)
    | k15_lattice3(sK6,X1_52) = k16_lattice3(sK6,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7721,c_3008,c_3803])).

cnf(c_19,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_517,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_518,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | r2_hidden(X0,a_2_2_lattice3(sK6,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,a_2_2_lattice3(sK6,X1))
    | ~ r4_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_32,c_31,c_29])).

cnf(c_523,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | r2_hidden(X0,a_2_2_lattice3(sK6,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_522])).

cnf(c_3018,plain,
    ( ~ r4_lattice3(sK6,X0_51,X0_52)
    | r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_523])).

cnf(c_34358,plain,
    ( ~ r4_lattice3(sK6,sK2(sK6,X0_52,k16_lattice3(sK6,a_2_2_lattice3(sK6,X1_52))),X1_52)
    | ~ r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X1_52)),X0_52)
    | ~ m1_subset_1(sK2(sK6,X0_52,k16_lattice3(sK6,a_2_2_lattice3(sK6,X1_52))),u1_struct_0(sK6))
    | k15_lattice3(sK6,X0_52) = k16_lattice3(sK6,a_2_2_lattice3(sK6,X1_52)) ),
    inference(resolution,[status(thm)],[c_21884,c_3018])).

cnf(c_9,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_604,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_605,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | r4_lattice3(sK6,sK2(sK6,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6)
    | k15_lattice3(sK6,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r4_lattice3(sK6,sK2(sK6,X1,X0),X1)
    | ~ r4_lattice3(sK6,X0,X1)
    | k15_lattice3(sK6,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_32,c_31,c_29])).

cnf(c_610,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | r4_lattice3(sK6,sK2(sK6,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k15_lattice3(sK6,X1) = X0 ),
    inference(renaming,[status(thm)],[c_609])).

cnf(c_3014,plain,
    ( ~ r4_lattice3(sK6,X0_51,X0_52)
    | r4_lattice3(sK6,sK2(sK6,X0_52,X0_51),X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | k15_lattice3(sK6,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_610])).

cnf(c_64876,plain,
    ( ~ r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X0_52)
    | ~ m1_subset_1(sK2(sK6,X0_52,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52))),u1_struct_0(sK6))
    | ~ m1_subset_1(k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),u1_struct_0(sK6))
    | k15_lattice3(sK6,X0_52) = k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)) ),
    inference(resolution,[status(thm)],[c_34358,c_3014])).

cnf(c_64889,plain,
    ( ~ r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X0_52)
    | k15_lattice3(sK6,X0_52) = k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_64876,c_3008,c_3015])).

cnf(c_64891,plain,
    ( ~ r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7)
    | k15_lattice3(sK6,sK7) = k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_64889])).

cnf(c_3027,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_3026,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_4113,plain,
    ( X0_51 != X1_51
    | X1_51 = X0_51 ),
    inference(resolution,[status(thm)],[c_3027,c_3026])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK4(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_670,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK4(X0,X1,X2) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_671,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1))
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6)
    | sK4(X0,sK6,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_675,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1))
    | sK4(X0,sK6,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_671,c_32,c_31,c_29])).

cnf(c_3011,plain,
    ( ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52))
    | sK4(X0_51,sK6,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_675])).

cnf(c_5054,plain,
    ( ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52))
    | X0_51 = sK4(X0_51,sK6,X0_52) ),
    inference(resolution,[status(thm)],[c_4113,c_3011])).

cnf(c_3032,plain,
    ( ~ r4_lattice3(X0_53,X0_51,X0_52)
    | r4_lattice3(X0_53,X1_51,X0_52)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_5777,plain,
    ( r4_lattice3(X0_53,X0_51,X0_52)
    | ~ r4_lattice3(X0_53,sK4(X0_51,sK6,X1_52),X0_52)
    | ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X1_52)) ),
    inference(resolution,[status(thm)],[c_5054,c_3032])).

cnf(c_20,plain,
    ( r4_lattice3(X0,sK4(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_499,plain,
    ( r4_lattice3(X0,sK4(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_500,plain,
    ( r4_lattice3(sK6,sK4(X0,sK6,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1))
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_504,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1))
    | r4_lattice3(sK6,sK4(X0,sK6,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_32,c_31,c_29])).

cnf(c_505,plain,
    ( r4_lattice3(sK6,sK4(X0,sK6,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1)) ),
    inference(renaming,[status(thm)],[c_504])).

cnf(c_3019,plain,
    ( r4_lattice3(sK6,sK4(X0_51,sK6,X0_52),X0_52)
    | ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52)) ),
    inference(subtyping,[status(esa)],[c_505])).

cnf(c_40075,plain,
    ( r4_lattice3(sK6,X0_51,X0_52)
    | ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52)) ),
    inference(resolution,[status(thm)],[c_5777,c_3019])).

cnf(c_1,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_944,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_29])).

cnf(c_945,plain,
    ( r3_lattice3(sK6,X0,X1)
    | r2_hidden(sK0(sK6,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(sK0(sK6,X0,X1),X1)
    | r3_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_32])).

cnf(c_950,plain,
    ( r3_lattice3(sK6,X0,X1)
    | r2_hidden(sK0(sK6,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_949])).

cnf(c_3000,plain,
    ( r3_lattice3(sK6,X0_51,X0_52)
    | r2_hidden(sK0(sK6,X0_51,X0_52),X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_950])).

cnf(c_40743,plain,
    ( r4_lattice3(sK6,sK0(sK6,X0_51,a_2_2_lattice3(sK6,X0_52)),X0_52)
    | r3_lattice3(sK6,X0_51,a_2_2_lattice3(sK6,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_40075,c_3000])).

cnf(c_7,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_806,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_807,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | r1_lattices(sK6,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK6,X2,X0)
    | ~ r4_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_807,c_32])).

cnf(c_812,plain,
    ( ~ r4_lattice3(sK6,X0,X1)
    | r1_lattices(sK6,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_811])).

cnf(c_3006,plain,
    ( ~ r4_lattice3(sK6,X0_51,X0_52)
    | r1_lattices(sK6,X1_51,X0_51)
    | ~ r2_hidden(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_812])).

cnf(c_40783,plain,
    ( r1_lattices(sK6,X0_51,sK0(sK6,X1_51,a_2_2_lattice3(sK6,X0_52)))
    | r3_lattice3(sK6,X1_51,a_2_2_lattice3(sK6,X0_52))
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6,X1_51,a_2_2_lattice3(sK6,X0_52)),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_40743,c_3006])).

cnf(c_2,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_923,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_29])).

cnf(c_924,plain,
    ( r3_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_923])).

cnf(c_928,plain,
    ( m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r3_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_924,c_32])).

cnf(c_929,plain,
    ( r3_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_928])).

cnf(c_3001,plain,
    ( r3_lattice3(sK6,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK6,X0_51,X0_52),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_929])).

cnf(c_61723,plain,
    ( r1_lattices(sK6,X0_51,sK0(sK6,X1_51,a_2_2_lattice3(sK6,X0_52)))
    | r3_lattice3(sK6,X1_51,a_2_2_lattice3(sK6,X0_52))
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_40783,c_3001])).

cnf(c_0,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_965,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_29])).

cnf(c_966,plain,
    ( ~ r1_lattices(sK6,X0,sK0(sK6,X0,X1))
    | r3_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r3_lattice3(sK6,X0,X1)
    | ~ r1_lattices(sK6,X0,sK0(sK6,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_32])).

cnf(c_971,plain,
    ( ~ r1_lattices(sK6,X0,sK0(sK6,X0,X1))
    | r3_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_970])).

cnf(c_2999,plain,
    ( ~ r1_lattices(sK6,X0_51,sK0(sK6,X0_51,X0_52))
    | r3_lattice3(sK6,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_971])).

cnf(c_61745,plain,
    ( r3_lattice3(sK6,X0_51,a_2_2_lattice3(sK6,X0_52))
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_61723,c_2999])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_795,plain,
    ( v2_struct_0(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_796,plain,
    ( v2_struct_0(sK6)
    | k15_lattice3(sK6,a_2_1_lattice3(sK6,X0)) = k16_lattice3(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_800,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,X0)) = k16_lattice3(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_796,c_32])).

cnf(c_3007,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)) = k16_lattice3(sK6,X0_52) ),
    inference(subtyping,[status(esa)],[c_800])).

cnf(c_5052,plain,
    ( k16_lattice3(sK6,X0_52) = k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)) ),
    inference(resolution,[status(thm)],[c_4113,c_3007])).

cnf(c_5363,plain,
    ( r4_lattice3(X0_53,k16_lattice3(sK6,X0_52),X1_52)
    | ~ r4_lattice3(X0_53,k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)),X1_52) ),
    inference(resolution,[status(thm)],[c_5052,c_3032])).

cnf(c_12,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_538,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_539,plain,
    ( r4_lattice3(sK6,k15_lattice3(sK6,X0),X0)
    | ~ m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6))
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_543,plain,
    ( ~ m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6))
    | r4_lattice3(sK6,k15_lattice3(sK6,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_32,c_31,c_29])).

cnf(c_544,plain,
    ( r4_lattice3(sK6,k15_lattice3(sK6,X0),X0)
    | ~ m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_3017,plain,
    ( r4_lattice3(sK6,k15_lattice3(sK6,X0_52),X0_52)
    | ~ m1_subset_1(k15_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_544])).

cnf(c_32959,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),a_2_1_lattice3(sK6,X0_52))
    | ~ m1_subset_1(k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_5363,c_3017])).

cnf(c_3575,plain,
    ( r4_lattice3(sK6,k15_lattice3(sK6,X0_52),X0_52) = iProver_top
    | m1_subset_1(k15_lattice3(sK6,X0_52),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3017])).

cnf(c_3886,plain,
    ( r4_lattice3(sK6,k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)),a_2_1_lattice3(sK6,X0_52)) = iProver_top
    | m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3007,c_3575])).

cnf(c_3087,plain,
    ( m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3008])).

cnf(c_3891,plain,
    ( r4_lattice3(sK6,k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)),a_2_1_lattice3(sK6,X0_52)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_3087])).

cnf(c_3897,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),a_2_1_lattice3(sK6,X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3007,c_3891])).

cnf(c_3898,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),a_2_1_lattice3(sK6,X0_52)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3897])).

cnf(c_34083,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),a_2_1_lattice3(sK6,X0_52)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32959,c_3898])).

cnf(c_34095,plain,
    ( r1_lattices(sK6,X0_51,k16_lattice3(sK6,X0_52))
    | ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_34083,c_3006])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1004,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | sK3(X0,X1,X2) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_1005,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1))
    | v2_struct_0(sK6)
    | sK3(X0,sK6,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1009,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1))
    | sK3(X0,sK6,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1005,c_32])).

cnf(c_2997,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
    | sK3(X0_51,sK6,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_1009])).

cnf(c_5048,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
    | X0_51 = sK3(X0_51,sK6,X0_52) ),
    inference(resolution,[status(thm)],[c_4113,c_2997])).

cnf(c_3030,plain,
    ( ~ m1_subset_1(X0_51,X0_54)
    | m1_subset_1(X1_51,X0_54)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_5654,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
    | m1_subset_1(X0_51,X0_54)
    | ~ m1_subset_1(sK3(X0_51,sK6,X0_52),X0_54) ),
    inference(resolution,[status(thm)],[c_5048,c_3030])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_986,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_987,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1))
    | m1_subset_1(sK3(X0,sK6,X1),u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_991,plain,
    ( m1_subset_1(sK3(X0,sK6,X1),u1_struct_0(sK6))
    | ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_987,c_32])).

cnf(c_992,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1))
    | m1_subset_1(sK3(X0,sK6,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_991])).

cnf(c_2998,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
    | m1_subset_1(sK3(X0_51,sK6,X0_52),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_992])).

cnf(c_33366,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
    | m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_5654,c_2998])).

cnf(c_34564,plain,
    ( r1_lattices(sK6,X0_51,k16_lattice3(sK6,X0_52))
    | ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34095,c_3008,c_33366])).

cnf(c_4,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_875,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_29])).

cnf(c_876,plain,
    ( r4_lattice3(sK6,X0,X1)
    | ~ r1_lattices(sK6,sK1(sK6,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_875])).

cnf(c_880,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_lattices(sK6,sK1(sK6,X0,X1),X0)
    | r4_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_876,c_32])).

cnf(c_881,plain,
    ( r4_lattice3(sK6,X0,X1)
    | ~ r1_lattices(sK6,sK1(sK6,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_880])).

cnf(c_3003,plain,
    ( r4_lattice3(sK6,X0_51,X0_52)
    | ~ r1_lattices(sK6,sK1(sK6,X0_51,X0_52),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_881])).

cnf(c_34582,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),a_2_1_lattice3(sK6,X0_52))
    | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_34564,c_3003])).

cnf(c_34605,plain,
    ( ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),a_2_1_lattice3(sK6,X0_52))
    | r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34582,c_3008])).

cnf(c_34606,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),a_2_1_lattice3(sK6,X0_52)) ),
    inference(renaming,[status(thm)],[c_34605])).

cnf(c_15,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_759,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_760,plain,
    ( ~ r3_lattice3(sK6,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK6,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,a_2_1_lattice3(sK6,X1))
    | ~ r3_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_32])).

cnf(c_765,plain,
    ( ~ r3_lattice3(sK6,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK6,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_764])).

cnf(c_3009,plain,
    ( ~ r3_lattice3(sK6,X0_51,X0_52)
    | r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_765])).

cnf(c_34798,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | ~ r3_lattice3(sK6,sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),X0_52)
    | ~ m1_subset_1(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_34606,c_3009])).

cnf(c_6,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_833,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_834,plain,
    ( r4_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_838,plain,
    ( m1_subset_1(sK1(sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r4_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_834,c_32])).

cnf(c_839,plain,
    ( r4_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_838])).

cnf(c_3005,plain,
    ( r4_lattice3(sK6,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0_51,X0_52),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_839])).

cnf(c_3665,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | m1_subset_1(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3005])).

cnf(c_34804,plain,
    ( ~ r3_lattice3(sK6,sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),X0_52)
    | r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34798,c_3008,c_3665])).

cnf(c_34805,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
    | ~ r3_lattice3(sK6,sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),X0_52) ),
    inference(renaming,[status(thm)],[c_34804])).

cnf(c_62004,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X1_52)
    | ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X1_52),X0_52)
    | ~ m1_subset_1(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X1_52),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_61745,c_34805])).

cnf(c_62006,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7)
    | ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7),sK7)
    | ~ m1_subset_1(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_62004])).

cnf(c_14777,plain,
    ( m1_subset_1(k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3008])).

cnf(c_9115,plain,
    ( r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7)
    | m1_subset_1(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3665])).

cnf(c_28,negated_conjecture,
    ( k15_lattice3(sK6,sK7) != k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3024,negated_conjecture,
    ( k15_lattice3(sK6,sK7) != k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_87989,c_64891,c_62006,c_14777,c_9115,c_3024])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.51/4.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.51/4.51  
% 31.51/4.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.51/4.51  
% 31.51/4.51  ------  iProver source info
% 31.51/4.51  
% 31.51/4.51  git: date: 2020-06-30 10:37:57 +0100
% 31.51/4.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.51/4.51  git: non_committed_changes: false
% 31.51/4.51  git: last_make_outside_of_git: false
% 31.51/4.51  
% 31.51/4.51  ------ 
% 31.51/4.51  ------ Parsing...
% 31.51/4.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.51/4.51  
% 31.51/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 31.51/4.51  
% 31.51/4.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.51/4.51  
% 31.51/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.51  ------ Proving...
% 31.51/4.51  ------ Problem Properties 
% 31.51/4.51  
% 31.51/4.51  
% 31.51/4.51  clauses                                 28
% 31.51/4.51  conjectures                             1
% 31.51/4.51  EPR                                     0
% 31.51/4.51  Horn                                    20
% 31.51/4.51  unary                                   4
% 31.51/4.51  binary                                  7
% 31.51/4.51  lits                                    80
% 31.51/4.51  lits eq                                 10
% 31.51/4.51  fd_pure                                 0
% 31.51/4.51  fd_pseudo                               0
% 31.51/4.51  fd_cond                                 0
% 31.51/4.51  fd_pseudo_cond                          5
% 31.51/4.51  AC symbols                              0
% 31.51/4.51  
% 31.51/4.51  ------ Input Options Time Limit: Unbounded
% 31.51/4.51  
% 31.51/4.51  
% 31.51/4.51  ------ 
% 31.51/4.51  Current options:
% 31.51/4.51  ------ 
% 31.51/4.51  
% 31.51/4.51  
% 31.51/4.51  
% 31.51/4.51  
% 31.51/4.51  ------ Proving...
% 31.51/4.51  
% 31.51/4.51  
% 31.51/4.51  % SZS status Theorem for theBenchmark.p
% 31.51/4.51  
% 31.51/4.51  % SZS output start CNFRefutation for theBenchmark.p
% 31.51/4.51  
% 31.51/4.51  fof(f2,axiom,(
% 31.51/4.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f13,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.51/4.51    inference(ennf_transformation,[],[f2])).
% 31.51/4.51  
% 31.51/4.51  fof(f14,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f13])).
% 31.51/4.51  
% 31.51/4.51  fof(f33,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(nnf_transformation,[],[f14])).
% 31.51/4.51  
% 31.51/4.51  fof(f34,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(rectify,[],[f33])).
% 31.51/4.51  
% 31.51/4.51  fof(f35,plain,(
% 31.51/4.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 31.51/4.51    introduced(choice_axiom,[])).
% 31.51/4.51  
% 31.51/4.51  fof(f36,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 31.51/4.51  
% 31.51/4.51  fof(f64,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f36])).
% 31.51/4.51  
% 31.51/4.51  fof(f9,conjecture,(
% 31.51/4.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f10,negated_conjecture,(
% 31.51/4.51    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 31.51/4.51    inference(negated_conjecture,[],[f9])).
% 31.51/4.51  
% 31.51/4.51  fof(f27,plain,(
% 31.51/4.51    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 31.51/4.51    inference(ennf_transformation,[],[f10])).
% 31.51/4.51  
% 31.51/4.51  fof(f28,plain,(
% 31.51/4.51    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f27])).
% 31.51/4.51  
% 31.51/4.51  fof(f56,plain,(
% 31.51/4.51    ( ! [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) => k15_lattice3(X0,sK7) != k16_lattice3(X0,a_2_2_lattice3(X0,sK7))) )),
% 31.51/4.51    introduced(choice_axiom,[])).
% 31.51/4.51  
% 31.51/4.51  fof(f55,plain,(
% 31.51/4.51    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : k15_lattice3(sK6,X1) != k16_lattice3(sK6,a_2_2_lattice3(sK6,X1)) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6))),
% 31.51/4.51    introduced(choice_axiom,[])).
% 31.51/4.51  
% 31.51/4.51  fof(f57,plain,(
% 31.51/4.51    k15_lattice3(sK6,sK7) != k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6)),
% 31.51/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f28,f56,f55])).
% 31.51/4.51  
% 31.51/4.51  fof(f89,plain,(
% 31.51/4.51    l3_lattices(sK6)),
% 31.51/4.51    inference(cnf_transformation,[],[f57])).
% 31.51/4.51  
% 31.51/4.51  fof(f86,plain,(
% 31.51/4.51    ~v2_struct_0(sK6)),
% 31.51/4.51    inference(cnf_transformation,[],[f57])).
% 31.51/4.51  
% 31.51/4.51  fof(f1,axiom,(
% 31.51/4.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f11,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.51/4.51    inference(ennf_transformation,[],[f1])).
% 31.51/4.51  
% 31.51/4.51  fof(f12,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f11])).
% 31.51/4.51  
% 31.51/4.51  fof(f29,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(nnf_transformation,[],[f12])).
% 31.51/4.51  
% 31.51/4.51  fof(f30,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(rectify,[],[f29])).
% 31.51/4.51  
% 31.51/4.51  fof(f31,plain,(
% 31.51/4.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 31.51/4.51    introduced(choice_axiom,[])).
% 31.51/4.51  
% 31.51/4.51  fof(f32,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 31.51/4.51  
% 31.51/4.51  fof(f58,plain,(
% 31.51/4.51    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f32])).
% 31.51/4.51  
% 31.51/4.51  fof(f8,axiom,(
% 31.51/4.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f25,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 31.51/4.51    inference(ennf_transformation,[],[f8])).
% 31.51/4.51  
% 31.51/4.51  fof(f26,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f25])).
% 31.51/4.51  
% 31.51/4.51  fof(f50,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(nnf_transformation,[],[f26])).
% 31.51/4.51  
% 31.51/4.51  fof(f51,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f50])).
% 31.51/4.51  
% 31.51/4.51  fof(f52,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(rectify,[],[f51])).
% 31.51/4.51  
% 31.51/4.51  fof(f53,plain,(
% 31.51/4.51    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK5(X0,X1,X2),X1) & r3_lattice3(X0,sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 31.51/4.51    introduced(choice_axiom,[])).
% 31.51/4.51  
% 31.51/4.51  fof(f54,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK5(X0,X1,X2),X1) & r3_lattice3(X0,sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f52,f53])).
% 31.51/4.51  
% 31.51/4.51  fof(f81,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f54])).
% 31.51/4.51  
% 31.51/4.51  fof(f96,plain,(
% 31.51/4.51    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(equality_resolution,[],[f81])).
% 31.51/4.51  
% 31.51/4.51  fof(f5,axiom,(
% 31.51/4.51    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f19,plain,(
% 31.51/4.51    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.51/4.51    inference(ennf_transformation,[],[f5])).
% 31.51/4.51  
% 31.51/4.51  fof(f20,plain,(
% 31.51/4.51    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f19])).
% 31.51/4.51  
% 31.51/4.51  fof(f72,plain,(
% 31.51/4.51    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f20])).
% 31.51/4.51  
% 31.51/4.51  fof(f88,plain,(
% 31.51/4.51    v4_lattice3(sK6)),
% 31.51/4.51    inference(cnf_transformation,[],[f57])).
% 31.51/4.51  
% 31.51/4.51  fof(f87,plain,(
% 31.51/4.51    v10_lattices(sK6)),
% 31.51/4.51    inference(cnf_transformation,[],[f57])).
% 31.51/4.51  
% 31.51/4.51  fof(f3,axiom,(
% 31.51/4.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f15,plain,(
% 31.51/4.51    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.51/4.51    inference(ennf_transformation,[],[f3])).
% 31.51/4.51  
% 31.51/4.51  fof(f16,plain,(
% 31.51/4.51    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f15])).
% 31.51/4.51  
% 31.51/4.51  fof(f37,plain,(
% 31.51/4.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(nnf_transformation,[],[f16])).
% 31.51/4.51  
% 31.51/4.51  fof(f38,plain,(
% 31.51/4.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f37])).
% 31.51/4.51  
% 31.51/4.51  fof(f39,plain,(
% 31.51/4.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(rectify,[],[f38])).
% 31.51/4.51  
% 31.51/4.51  fof(f40,plain,(
% 31.51/4.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 31.51/4.51    introduced(choice_axiom,[])).
% 31.51/4.51  
% 31.51/4.51  fof(f41,plain,(
% 31.51/4.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 31.51/4.51  
% 31.51/4.51  fof(f70,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK2(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f41])).
% 31.51/4.51  
% 31.51/4.51  fof(f68,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f41])).
% 31.51/4.51  
% 31.51/4.51  fof(f7,axiom,(
% 31.51/4.51    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f23,plain,(
% 31.51/4.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 31.51/4.51    inference(ennf_transformation,[],[f7])).
% 31.51/4.51  
% 31.51/4.51  fof(f24,plain,(
% 31.51/4.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.51/4.51    inference(flattening,[],[f23])).
% 31.51/4.51  
% 31.51/4.51  fof(f46,plain,(
% 31.51/4.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.51/4.51    inference(nnf_transformation,[],[f24])).
% 31.51/4.51  
% 31.51/4.51  fof(f47,plain,(
% 31.51/4.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.51/4.51    inference(rectify,[],[f46])).
% 31.51/4.51  
% 31.51/4.51  fof(f48,plain,(
% 31.51/4.51    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK4(X0,X1,X2),X2) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 31.51/4.51    introduced(choice_axiom,[])).
% 31.51/4.51  
% 31.51/4.51  fof(f49,plain,(
% 31.51/4.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK4(X0,X1,X2),X2) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.51/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).
% 31.51/4.51  
% 31.51/4.51  fof(f80,plain,(
% 31.51/4.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f49])).
% 31.51/4.51  
% 31.51/4.51  fof(f94,plain,(
% 31.51/4.51    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.51/4.51    inference(equality_resolution,[],[f80])).
% 31.51/4.51  
% 31.51/4.51  fof(f69,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK2(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f41])).
% 31.51/4.51  
% 31.51/4.51  fof(f78,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f49])).
% 31.51/4.51  
% 31.51/4.51  fof(f79,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK4(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f49])).
% 31.51/4.51  
% 31.51/4.51  fof(f60,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f32])).
% 31.51/4.51  
% 31.51/4.51  fof(f62,plain,(
% 31.51/4.51    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f36])).
% 31.51/4.51  
% 31.51/4.51  fof(f59,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f32])).
% 31.51/4.51  
% 31.51/4.51  fof(f61,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f32])).
% 31.51/4.51  
% 31.51/4.51  fof(f4,axiom,(
% 31.51/4.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f17,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.51/4.51    inference(ennf_transformation,[],[f4])).
% 31.51/4.51  
% 31.51/4.51  fof(f18,plain,(
% 31.51/4.51    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.51/4.51    inference(flattening,[],[f17])).
% 31.51/4.51  
% 31.51/4.51  fof(f71,plain,(
% 31.51/4.51    ( ! [X0,X1] : (k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f18])).
% 31.51/4.51  
% 31.51/4.51  fof(f66,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f41])).
% 31.51/4.51  
% 31.51/4.51  fof(f92,plain,(
% 31.51/4.51    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(equality_resolution,[],[f66])).
% 31.51/4.51  
% 31.51/4.51  fof(f6,axiom,(
% 31.51/4.51    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 31.51/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.51  
% 31.51/4.51  fof(f21,plain,(
% 31.51/4.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 31.51/4.51    inference(ennf_transformation,[],[f6])).
% 31.51/4.51  
% 31.51/4.51  fof(f22,plain,(
% 31.51/4.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 31.51/4.51    inference(flattening,[],[f21])).
% 31.51/4.51  
% 31.51/4.51  fof(f42,plain,(
% 31.51/4.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 31.51/4.51    inference(nnf_transformation,[],[f22])).
% 31.51/4.51  
% 31.51/4.51  fof(f43,plain,(
% 31.51/4.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 31.51/4.51    inference(rectify,[],[f42])).
% 31.51/4.51  
% 31.51/4.51  fof(f44,plain,(
% 31.51/4.51    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 31.51/4.51    introduced(choice_axiom,[])).
% 31.51/4.51  
% 31.51/4.51  fof(f45,plain,(
% 31.51/4.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 31.51/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 31.51/4.51  
% 31.51/4.51  fof(f74,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f45])).
% 31.51/4.51  
% 31.51/4.51  fof(f73,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f45])).
% 31.51/4.51  
% 31.51/4.51  fof(f65,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f36])).
% 31.51/4.51  
% 31.51/4.51  fof(f76,plain,(
% 31.51/4.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f45])).
% 31.51/4.51  
% 31.51/4.51  fof(f93,plain,(
% 31.51/4.51    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.51/4.51    inference(equality_resolution,[],[f76])).
% 31.51/4.51  
% 31.51/4.51  fof(f63,plain,(
% 31.51/4.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.51/4.51    inference(cnf_transformation,[],[f36])).
% 31.51/4.51  
% 31.51/4.51  fof(f90,plain,(
% 31.51/4.51    k15_lattice3(sK6,sK7) != k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7))),
% 31.51/4.51    inference(cnf_transformation,[],[f57])).
% 31.51/4.51  
% 31.51/4.51  cnf(c_5,plain,
% 31.51/4.51      ( r4_lattice3(X0,X1,X2)
% 31.51/4.51      | r2_hidden(sK1(X0,X1,X2),X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f64]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_29,negated_conjecture,
% 31.51/4.51      ( l3_lattices(sK6) ),
% 31.51/4.51      inference(cnf_transformation,[],[f89]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_854,plain,
% 31.51/4.51      ( r4_lattice3(X0,X1,X2)
% 31.51/4.51      | r2_hidden(sK1(X0,X1,X2),X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_5,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_855,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | r2_hidden(sK1(sK6,X0,X1),X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_854]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_32,negated_conjecture,
% 31.51/4.51      ( ~ v2_struct_0(sK6) ),
% 31.51/4.51      inference(cnf_transformation,[],[f86]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_859,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | r2_hidden(sK1(sK6,X0,X1),X1)
% 31.51/4.51      | r4_lattice3(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_855,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_860,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | r2_hidden(sK1(sK6,X0,X1),X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_859]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3004,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | r2_hidden(sK1(sK6,X0_51,X0_52),X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_860]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3692,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | r2_hidden(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),X1_52)
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(instantiation,[status(thm)],[c_3004]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_87989,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7)
% 31.51/4.51      | r2_hidden(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7),sK7)
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(instantiation,[status(thm)],[c_3692]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3,plain,
% 31.51/4.51      ( r1_lattices(X0,X1,X2)
% 31.51/4.51      | ~ r3_lattice3(X0,X1,X3)
% 31.51/4.51      | ~ r2_hidden(X2,X3)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f58]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_896,plain,
% 31.51/4.51      ( r1_lattices(X0,X1,X2)
% 31.51/4.51      | ~ r3_lattice3(X0,X1,X3)
% 31.51/4.51      | ~ r2_hidden(X2,X3)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_3,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_897,plain,
% 31.51/4.51      ( r1_lattices(sK6,X0,X1)
% 31.51/4.51      | ~ r3_lattice3(sK6,X0,X2)
% 31.51/4.51      | ~ r2_hidden(X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_896]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_901,plain,
% 31.51/4.51      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ r2_hidden(X1,X2)
% 31.51/4.51      | ~ r3_lattice3(sK6,X0,X2)
% 31.51/4.51      | r1_lattices(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_897,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_902,plain,
% 31.51/4.51      ( r1_lattices(sK6,X0,X1)
% 31.51/4.51      | ~ r3_lattice3(sK6,X0,X2)
% 31.51/4.51      | ~ r2_hidden(X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_901]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3002,plain,
% 31.51/4.51      ( r1_lattices(sK6,X0_51,X1_51)
% 31.51/4.51      | ~ r3_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | ~ r2_hidden(X1_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X1_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_902]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_27,plain,
% 31.51/4.51      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | ~ v4_lattice3(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f96]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_14,plain,
% 31.51/4.51      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f72]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_190,plain,
% 31.51/4.51      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | ~ v4_lattice3(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_27,c_14]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_30,negated_conjecture,
% 31.51/4.51      ( v4_lattice3(sK6) ),
% 31.51/4.51      inference(cnf_transformation,[],[f88]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_436,plain,
% 31.51/4.51      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_190,c_30]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_437,plain,
% 31.51/4.51      ( r3_lattice3(sK6,k16_lattice3(sK6,X0),X0)
% 31.51/4.51      | ~ v10_lattices(sK6)
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | ~ l3_lattices(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_436]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_31,negated_conjecture,
% 31.51/4.51      ( v10_lattices(sK6) ),
% 31.51/4.51      inference(cnf_transformation,[],[f87]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_441,plain,
% 31.51/4.51      ( r3_lattice3(sK6,k16_lattice3(sK6,X0),X0) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_437,c_32,c_31,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3022,plain,
% 31.51/4.51      ( r3_lattice3(sK6,k16_lattice3(sK6,X0_52),X0_52) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_441]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_4748,plain,
% 31.51/4.51      ( r1_lattices(sK6,k16_lattice3(sK6,X0_52),X0_51)
% 31.51/4.51      | ~ r2_hidden(X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_3002,c_3022]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_780,plain,
% 31.51/4.51      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_781,plain,
% 31.51/4.51      ( m1_subset_1(k16_lattice3(sK6,X0),u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_780]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_785,plain,
% 31.51/4.51      ( m1_subset_1(k16_lattice3(sK6,X0),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_781,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3008,plain,
% 31.51/4.51      ( m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_785]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_7697,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | ~ r2_hidden(X0_51,X0_52)
% 31.51/4.51      | r1_lattices(sK6,k16_lattice3(sK6,X0_52),X0_51) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_4748,c_3008]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_7698,plain,
% 31.51/4.51      ( r1_lattices(sK6,k16_lattice3(sK6,X0_52),X0_51)
% 31.51/4.51      | ~ r2_hidden(X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_7697]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_8,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | ~ v4_lattice3(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | k15_lattice3(X0,X2) = X1 ),
% 31.51/4.51      inference(cnf_transformation,[],[f70]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_628,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | k15_lattice3(X0,X2) = X1
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_8,c_30]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_629,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ r1_lattices(sK6,X0,sK2(sK6,X1,X0))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ v10_lattices(sK6)
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | ~ l3_lattices(sK6)
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_628]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_633,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ r1_lattices(sK6,X0,sK2(sK6,X1,X0))
% 31.51/4.51      | ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_629,c_32,c_31,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_634,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ r1_lattices(sK6,X0,sK2(sK6,X1,X0))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_633]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3013,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | ~ r1_lattices(sK6,X0_51,sK2(sK6,X0_52,X0_51))
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X0_52) = X0_51 ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_634]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_7721,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | ~ r2_hidden(sK2(sK6,X1_52,k16_lattice3(sK6,X0_52)),X0_52)
% 31.51/4.51      | ~ m1_subset_1(sK2(sK6,X1_52,k16_lattice3(sK6,X0_52)),u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X1_52) = k16_lattice3(sK6,X0_52) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_7698,c_3013]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_10,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | ~ v4_lattice3(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | k15_lattice3(X0,X2) = X1 ),
% 31.51/4.51      inference(cnf_transformation,[],[f68]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_580,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | k15_lattice3(X0,X2) = X1
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_581,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
% 31.51/4.51      | ~ v10_lattices(sK6)
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | ~ l3_lattices(sK6)
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_580]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_585,plain,
% 31.51/4.51      ( m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_581,c_32,c_31,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_586,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK2(sK6,X1,X0),u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_585]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3015,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK2(sK6,X0_52,X0_51),u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X0_52) = X0_51 ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_586]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3803,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | m1_subset_1(sK2(sK6,X1_52,k16_lattice3(sK6,X0_52)),u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X1_52) = k16_lattice3(sK6,X0_52) ),
% 31.51/4.51      inference(instantiation,[status(thm)],[c_3015]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_21884,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | ~ r2_hidden(sK2(sK6,X1_52,k16_lattice3(sK6,X0_52)),X0_52)
% 31.51/4.51      | k15_lattice3(sK6,X1_52) = k16_lattice3(sK6,X0_52) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_7721,c_3008,c_3803]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_19,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | ~ v4_lattice3(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f94]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_517,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_518,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | r2_hidden(X0,a_2_2_lattice3(sK6,X1))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ v10_lattices(sK6)
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | ~ l3_lattices(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_517]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_522,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | r2_hidden(X0,a_2_2_lattice3(sK6,X1))
% 31.51/4.51      | ~ r4_lattice3(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_518,c_32,c_31,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_523,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | r2_hidden(X0,a_2_2_lattice3(sK6,X1))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_522]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3018,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_523]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34358,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,sK2(sK6,X0_52,k16_lattice3(sK6,a_2_2_lattice3(sK6,X1_52))),X1_52)
% 31.51/4.51      | ~ r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X1_52)),X0_52)
% 31.51/4.51      | ~ m1_subset_1(sK2(sK6,X0_52,k16_lattice3(sK6,a_2_2_lattice3(sK6,X1_52))),u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X0_52) = k16_lattice3(sK6,a_2_2_lattice3(sK6,X1_52)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_21884,c_3018]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_9,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | ~ v4_lattice3(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | k15_lattice3(X0,X2) = X1 ),
% 31.51/4.51      inference(cnf_transformation,[],[f69]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_604,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | k15_lattice3(X0,X2) = X1
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_605,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | r4_lattice3(sK6,sK2(sK6,X1,X0),X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ v10_lattices(sK6)
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | ~ l3_lattices(sK6)
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_604]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_609,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | r4_lattice3(sK6,sK2(sK6,X1,X0),X1)
% 31.51/4.51      | ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_605,c_32,c_31,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_610,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | r4_lattice3(sK6,sK2(sK6,X1,X0),X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X1) = X0 ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_609]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3014,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | r4_lattice3(sK6,sK2(sK6,X0_52,X0_51),X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X0_52) = X0_51 ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_610]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_64876,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X0_52)
% 31.51/4.51      | ~ m1_subset_1(sK2(sK6,X0_52,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52))),u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),u1_struct_0(sK6))
% 31.51/4.51      | k15_lattice3(sK6,X0_52) = k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_34358,c_3014]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_64889,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X0_52)
% 31.51/4.51      | k15_lattice3(sK6,X0_52) = k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(forward_subsumption_resolution,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_64876,c_3008,c_3015]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_64891,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7)
% 31.51/4.51      | k15_lattice3(sK6,sK7) = k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)) ),
% 31.51/4.51      inference(instantiation,[status(thm)],[c_64889]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3027,plain,
% 31.51/4.51      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 31.51/4.51      theory(equality) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3026,plain,( X0_51 = X0_51 ),theory(equality) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_4113,plain,
% 31.51/4.51      ( X0_51 != X1_51 | X1_51 = X0_51 ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_3027,c_3026]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_21,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 31.51/4.51      | ~ v10_lattices(X1)
% 31.51/4.51      | ~ v4_lattice3(X1)
% 31.51/4.51      | v2_struct_0(X1)
% 31.51/4.51      | ~ l3_lattices(X1)
% 31.51/4.51      | sK4(X0,X1,X2) = X0 ),
% 31.51/4.51      inference(cnf_transformation,[],[f78]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_670,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 31.51/4.51      | ~ v10_lattices(X1)
% 31.51/4.51      | v2_struct_0(X1)
% 31.51/4.51      | ~ l3_lattices(X1)
% 31.51/4.51      | sK4(X0,X1,X2) = X0
% 31.51/4.51      | sK6 != X1 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_671,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1))
% 31.51/4.51      | ~ v10_lattices(sK6)
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | ~ l3_lattices(sK6)
% 31.51/4.51      | sK4(X0,sK6,X1) = X0 ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_670]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_675,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1)) | sK4(X0,sK6,X1) = X0 ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_671,c_32,c_31,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3011,plain,
% 31.51/4.51      ( ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52))
% 31.51/4.51      | sK4(X0_51,sK6,X0_52) = X0_51 ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_675]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_5054,plain,
% 31.51/4.51      ( ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52))
% 31.51/4.51      | X0_51 = sK4(X0_51,sK6,X0_52) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_4113,c_3011]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3032,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0_53,X0_51,X0_52)
% 31.51/4.51      | r4_lattice3(X0_53,X1_51,X0_52)
% 31.51/4.51      | X1_51 != X0_51 ),
% 31.51/4.51      theory(equality) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_5777,plain,
% 31.51/4.51      ( r4_lattice3(X0_53,X0_51,X0_52)
% 31.51/4.51      | ~ r4_lattice3(X0_53,sK4(X0_51,sK6,X1_52),X0_52)
% 31.51/4.51      | ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X1_52)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_5054,c_3032]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_20,plain,
% 31.51/4.51      ( r4_lattice3(X0,sK4(X1,X0,X2),X2)
% 31.51/4.51      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | ~ v4_lattice3(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f79]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_499,plain,
% 31.51/4.51      ( r4_lattice3(X0,sK4(X1,X0,X2),X2)
% 31.51/4.51      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_500,plain,
% 31.51/4.51      ( r4_lattice3(sK6,sK4(X0,sK6,X1),X1)
% 31.51/4.51      | ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1))
% 31.51/4.51      | ~ v10_lattices(sK6)
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | ~ l3_lattices(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_499]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_504,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1))
% 31.51/4.51      | r4_lattice3(sK6,sK4(X0,sK6,X1),X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_500,c_32,c_31,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_505,plain,
% 31.51/4.51      ( r4_lattice3(sK6,sK4(X0,sK6,X1),X1)
% 31.51/4.51      | ~ r2_hidden(X0,a_2_2_lattice3(sK6,X1)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_504]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3019,plain,
% 31.51/4.51      ( r4_lattice3(sK6,sK4(X0_51,sK6,X0_52),X0_52)
% 31.51/4.51      | ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_505]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_40075,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | ~ r2_hidden(X0_51,a_2_2_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_5777,c_3019]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_1,plain,
% 31.51/4.51      ( r3_lattice3(X0,X1,X2)
% 31.51/4.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f60]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_944,plain,
% 31.51/4.51      ( r3_lattice3(X0,X1,X2)
% 31.51/4.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_1,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_945,plain,
% 31.51/4.51      ( r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | r2_hidden(sK0(sK6,X0,X1),X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_944]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_949,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | r2_hidden(sK0(sK6,X0,X1),X1)
% 31.51/4.51      | r3_lattice3(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_945,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_950,plain,
% 31.51/4.51      ( r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | r2_hidden(sK0(sK6,X0,X1),X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_949]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3000,plain,
% 31.51/4.51      ( r3_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | r2_hidden(sK0(sK6,X0_51,X0_52),X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_950]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_40743,plain,
% 31.51/4.51      ( r4_lattice3(sK6,sK0(sK6,X0_51,a_2_2_lattice3(sK6,X0_52)),X0_52)
% 31.51/4.51      | r3_lattice3(sK6,X0_51,a_2_2_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_40075,c_3000]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_7,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | r1_lattices(X0,X3,X1)
% 31.51/4.51      | ~ r2_hidden(X3,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f62]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_806,plain,
% 31.51/4.51      ( ~ r4_lattice3(X0,X1,X2)
% 31.51/4.51      | r1_lattices(X0,X3,X1)
% 31.51/4.51      | ~ r2_hidden(X3,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_807,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | r1_lattices(sK6,X2,X0)
% 31.51/4.51      | ~ r2_hidden(X2,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_806]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_811,plain,
% 31.51/4.51      ( ~ m1_subset_1(X2,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ r2_hidden(X2,X1)
% 31.51/4.51      | r1_lattices(sK6,X2,X0)
% 31.51/4.51      | ~ r4_lattice3(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_807,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_812,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | r1_lattices(sK6,X2,X0)
% 31.51/4.51      | ~ r2_hidden(X2,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X2,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_811]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3006,plain,
% 31.51/4.51      ( ~ r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | r1_lattices(sK6,X1_51,X0_51)
% 31.51/4.51      | ~ r2_hidden(X1_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X1_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_812]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_40783,plain,
% 31.51/4.51      ( r1_lattices(sK6,X0_51,sK0(sK6,X1_51,a_2_2_lattice3(sK6,X0_52)))
% 31.51/4.51      | r3_lattice3(sK6,X1_51,a_2_2_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ r2_hidden(X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X1_51,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(sK0(sK6,X1_51,a_2_2_lattice3(sK6,X0_52)),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_40743,c_3006]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_2,plain,
% 31.51/4.51      ( r3_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f59]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_923,plain,
% 31.51/4.51      ( r3_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_2,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_924,plain,
% 31.51/4.51      ( r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_923]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_928,plain,
% 31.51/4.51      ( m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | r3_lattice3(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_924,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_929,plain,
% 31.51/4.51      ( r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_928]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3001,plain,
% 31.51/4.51      ( r3_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK0(sK6,X0_51,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_929]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_61723,plain,
% 31.51/4.51      ( r1_lattices(sK6,X0_51,sK0(sK6,X1_51,a_2_2_lattice3(sK6,X0_52)))
% 31.51/4.51      | r3_lattice3(sK6,X1_51,a_2_2_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ r2_hidden(X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X1_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(forward_subsumption_resolution,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_40783,c_3001]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_0,plain,
% 31.51/4.51      ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 31.51/4.51      | r3_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f61]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_965,plain,
% 31.51/4.51      ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 31.51/4.51      | r3_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_0,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_966,plain,
% 31.51/4.51      ( ~ r1_lattices(sK6,X0,sK0(sK6,X0,X1))
% 31.51/4.51      | r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_965]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_970,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ r1_lattices(sK6,X0,sK0(sK6,X0,X1)) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_966,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_971,plain,
% 31.51/4.51      ( ~ r1_lattices(sK6,X0,sK0(sK6,X0,X1))
% 31.51/4.51      | r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_970]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_2999,plain,
% 31.51/4.51      ( ~ r1_lattices(sK6,X0_51,sK0(sK6,X0_51,X0_52))
% 31.51/4.51      | r3_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_971]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_61745,plain,
% 31.51/4.51      ( r3_lattice3(sK6,X0_51,a_2_2_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ r2_hidden(X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_61723,c_2999]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_13,plain,
% 31.51/4.51      ( v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
% 31.51/4.51      inference(cnf_transformation,[],[f71]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_795,plain,
% 31.51/4.51      ( v2_struct_0(X0)
% 31.51/4.51      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_796,plain,
% 31.51/4.51      ( v2_struct_0(sK6)
% 31.51/4.51      | k15_lattice3(sK6,a_2_1_lattice3(sK6,X0)) = k16_lattice3(sK6,X0) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_795]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_800,plain,
% 31.51/4.51      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,X0)) = k16_lattice3(sK6,X0) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_796,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3007,plain,
% 31.51/4.51      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)) = k16_lattice3(sK6,X0_52) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_800]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_5052,plain,
% 31.51/4.51      ( k16_lattice3(sK6,X0_52) = k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_4113,c_3007]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_5363,plain,
% 31.51/4.51      ( r4_lattice3(X0_53,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | ~ r4_lattice3(X0_53,k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)),X1_52) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_5052,c_3032]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_12,plain,
% 31.51/4.51      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 31.51/4.51      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | ~ v4_lattice3(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f92]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_538,plain,
% 31.51/4.51      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 31.51/4.51      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 31.51/4.51      | ~ v10_lattices(X0)
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_539,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k15_lattice3(sK6,X0),X0)
% 31.51/4.51      | ~ m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6))
% 31.51/4.51      | ~ v10_lattices(sK6)
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | ~ l3_lattices(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_538]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_543,plain,
% 31.51/4.51      ( ~ m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6))
% 31.51/4.51      | r4_lattice3(sK6,k15_lattice3(sK6,X0),X0) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_539,c_32,c_31,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_544,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k15_lattice3(sK6,X0),X0)
% 31.51/4.51      | ~ m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_543]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3017,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k15_lattice3(sK6,X0_52),X0_52)
% 31.51/4.51      | ~ m1_subset_1(k15_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_544]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_32959,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ m1_subset_1(k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_5363,c_3017]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3575,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k15_lattice3(sK6,X0_52),X0_52) = iProver_top
% 31.51/4.51      | m1_subset_1(k15_lattice3(sK6,X0_52),u1_struct_0(sK6)) != iProver_top ),
% 31.51/4.51      inference(predicate_to_equality,[status(thm)],[c_3017]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3886,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)),a_2_1_lattice3(sK6,X0_52)) = iProver_top
% 31.51/4.51      | m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) != iProver_top ),
% 31.51/4.51      inference(superposition,[status(thm)],[c_3007,c_3575]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3087,plain,
% 31.51/4.51      ( m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) = iProver_top ),
% 31.51/4.51      inference(predicate_to_equality,[status(thm)],[c_3008]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3891,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k15_lattice3(sK6,a_2_1_lattice3(sK6,X0_52)),a_2_1_lattice3(sK6,X0_52)) = iProver_top ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_3886,c_3087]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3897,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),a_2_1_lattice3(sK6,X0_52)) = iProver_top ),
% 31.51/4.51      inference(superposition,[status(thm)],[c_3007,c_3891]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3898,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),a_2_1_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_3897]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34083,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),a_2_1_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_32959,c_3898]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34095,plain,
% 31.51/4.51      ( r1_lattices(sK6,X0_51,k16_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_34083,c_3006]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_17,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 31.51/4.51      | v2_struct_0(X1)
% 31.51/4.51      | ~ l3_lattices(X1)
% 31.51/4.51      | sK3(X0,X1,X2) = X0 ),
% 31.51/4.51      inference(cnf_transformation,[],[f74]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_1004,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 31.51/4.51      | v2_struct_0(X1)
% 31.51/4.51      | sK3(X0,X1,X2) = X0
% 31.51/4.51      | sK6 != X1 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_1005,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1))
% 31.51/4.51      | v2_struct_0(sK6)
% 31.51/4.51      | sK3(X0,sK6,X1) = X0 ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_1004]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_1009,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1)) | sK3(X0,sK6,X1) = X0 ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_1005,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_2997,plain,
% 31.51/4.51      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | sK3(X0_51,sK6,X0_52) = X0_51 ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_1009]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_5048,plain,
% 31.51/4.51      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | X0_51 = sK3(X0_51,sK6,X0_52) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_4113,c_2997]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3030,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0_51,X0_54)
% 31.51/4.51      | m1_subset_1(X1_51,X0_54)
% 31.51/4.51      | X1_51 != X0_51 ),
% 31.51/4.51      theory(equality) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_5654,plain,
% 31.51/4.51      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | m1_subset_1(X0_51,X0_54)
% 31.51/4.51      | ~ m1_subset_1(sK3(X0_51,sK6,X0_52),X0_54) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_5048,c_3030]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_18,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 31.51/4.51      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 31.51/4.51      | v2_struct_0(X1)
% 31.51/4.51      | ~ l3_lattices(X1) ),
% 31.51/4.51      inference(cnf_transformation,[],[f73]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_986,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 31.51/4.51      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 31.51/4.51      | v2_struct_0(X1)
% 31.51/4.51      | sK6 != X1 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_987,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1))
% 31.51/4.51      | m1_subset_1(sK3(X0,sK6,X1),u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_986]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_991,plain,
% 31.51/4.51      ( m1_subset_1(sK3(X0,sK6,X1),u1_struct_0(sK6))
% 31.51/4.51      | ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1)) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_987,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_992,plain,
% 31.51/4.51      ( ~ r2_hidden(X0,a_2_1_lattice3(sK6,X1))
% 31.51/4.51      | m1_subset_1(sK3(X0,sK6,X1),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_991]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_2998,plain,
% 31.51/4.51      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | m1_subset_1(sK3(X0_51,sK6,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_992]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_33366,plain,
% 31.51/4.51      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_5654,c_2998]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34564,plain,
% 31.51/4.51      ( r1_lattices(sK6,X0_51,k16_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_34095,c_3008,c_33366]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_4,plain,
% 31.51/4.51      ( r4_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f65]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_875,plain,
% 31.51/4.51      ( r4_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_4,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_876,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ r1_lattices(sK6,sK1(sK6,X0,X1),X0)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_875]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_880,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | ~ r1_lattices(sK6,sK1(sK6,X0,X1),X0)
% 31.51/4.51      | r4_lattice3(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_876,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_881,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ r1_lattices(sK6,sK1(sK6,X0,X1),X0)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_880]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3003,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | ~ r1_lattices(sK6,sK1(sK6,X0_51,X0_52),X0_51)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_881]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34582,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_34564,c_3003]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34605,plain,
% 31.51/4.51      ( ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_34582,c_3008]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34606,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),a_2_1_lattice3(sK6,X0_52)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_34605]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_15,plain,
% 31.51/4.51      ( ~ r3_lattice3(X0,X1,X2)
% 31.51/4.51      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f93]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_759,plain,
% 31.51/4.51      ( ~ r3_lattice3(X0,X1,X2)
% 31.51/4.51      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_760,plain,
% 31.51/4.51      ( ~ r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | r2_hidden(X0,a_2_1_lattice3(sK6,X1))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_759]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_764,plain,
% 31.51/4.51      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | r2_hidden(X0,a_2_1_lattice3(sK6,X1))
% 31.51/4.51      | ~ r3_lattice3(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_760,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_765,plain,
% 31.51/4.51      ( ~ r3_lattice3(sK6,X0,X1)
% 31.51/4.51      | r2_hidden(X0,a_2_1_lattice3(sK6,X1))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_764]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3009,plain,
% 31.51/4.51      ( ~ r3_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | r2_hidden(X0_51,a_2_1_lattice3(sK6,X0_52))
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_765]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34798,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | ~ r3_lattice3(sK6,sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),X0_52)
% 31.51/4.51      | ~ m1_subset_1(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_34606,c_3009]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_6,plain,
% 31.51/4.51      ( r4_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | ~ l3_lattices(X0) ),
% 31.51/4.51      inference(cnf_transformation,[],[f63]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_833,plain,
% 31.51/4.51      ( r4_lattice3(X0,X1,X2)
% 31.51/4.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.51/4.51      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 31.51/4.51      | v2_struct_0(X0)
% 31.51/4.51      | sK6 != X0 ),
% 31.51/4.51      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_834,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK1(sK6,X0,X1),u1_struct_0(sK6))
% 31.51/4.51      | v2_struct_0(sK6) ),
% 31.51/4.51      inference(unflattening,[status(thm)],[c_833]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_838,plain,
% 31.51/4.51      ( m1_subset_1(sK1(sK6,X0,X1),u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | r4_lattice3(sK6,X0,X1) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_834,c_32]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_839,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0,X1)
% 31.51/4.51      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK1(sK6,X0,X1),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_838]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3005,plain,
% 31.51/4.51      ( r4_lattice3(sK6,X0_51,X0_52)
% 31.51/4.51      | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
% 31.51/4.51      | m1_subset_1(sK1(sK6,X0_51,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_839]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3665,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | m1_subset_1(sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,X0_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(instantiation,[status(thm)],[c_3005]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34804,plain,
% 31.51/4.51      ( ~ r3_lattice3(sK6,sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),X0_52)
% 31.51/4.51      | r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52) ),
% 31.51/4.51      inference(global_propositional_subsumption,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_34798,c_3008,c_3665]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_34805,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,X0_52),X1_52)
% 31.51/4.51      | ~ r3_lattice3(sK6,sK1(sK6,k16_lattice3(sK6,X0_52),X1_52),X0_52) ),
% 31.51/4.51      inference(renaming,[status(thm)],[c_34804]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_62004,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X1_52)
% 31.51/4.51      | ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X1_52),X0_52)
% 31.51/4.51      | ~ m1_subset_1(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,X0_52)),X1_52),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(resolution,[status(thm)],[c_61745,c_34805]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_62006,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7)
% 31.51/4.51      | ~ r2_hidden(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7),sK7)
% 31.51/4.51      | ~ m1_subset_1(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(instantiation,[status(thm)],[c_62004]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_14777,plain,
% 31.51/4.51      ( m1_subset_1(k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(instantiation,[status(thm)],[c_3008]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_9115,plain,
% 31.51/4.51      ( r4_lattice3(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7)
% 31.51/4.51      | m1_subset_1(sK1(sK6,k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),sK7),u1_struct_0(sK6))
% 31.51/4.51      | ~ m1_subset_1(k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)),u1_struct_0(sK6)) ),
% 31.51/4.51      inference(instantiation,[status(thm)],[c_3665]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_28,negated_conjecture,
% 31.51/4.51      ( k15_lattice3(sK6,sK7) != k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)) ),
% 31.51/4.51      inference(cnf_transformation,[],[f90]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(c_3024,negated_conjecture,
% 31.51/4.51      ( k15_lattice3(sK6,sK7) != k16_lattice3(sK6,a_2_2_lattice3(sK6,sK7)) ),
% 31.51/4.51      inference(subtyping,[status(esa)],[c_28]) ).
% 31.51/4.51  
% 31.51/4.51  cnf(contradiction,plain,
% 31.51/4.51      ( $false ),
% 31.51/4.51      inference(minisat,
% 31.51/4.51                [status(thm)],
% 31.51/4.51                [c_87989,c_64891,c_62006,c_14777,c_9115,c_3024]) ).
% 31.51/4.51  
% 31.51/4.51  
% 31.51/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.51/4.51  
% 31.51/4.51  ------                               Statistics
% 31.51/4.51  
% 31.51/4.51  ------ Selected
% 31.51/4.51  
% 31.51/4.51  total_time:                             3.854
% 31.51/4.51  
%------------------------------------------------------------------------------

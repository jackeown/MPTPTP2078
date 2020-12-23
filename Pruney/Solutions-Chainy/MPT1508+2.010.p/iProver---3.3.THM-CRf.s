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
% DateTime   : Thu Dec  3 12:19:14 EST 2020

% Result     : Theorem 15.47s
% Output     : CNFRefutation 15.47s
% Verified   : 
% Statistics : Number of formulae       :  184 (2206 expanded)
%              Number of clauses        :  112 ( 540 expanded)
%              Number of leaves         :   15 ( 657 expanded)
%              Depth                    :   44
%              Number of atoms          : 1128 (15706 expanded)
%              Number of equality atoms :  400 (3010 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK5(X0,X1,X2),X1)
        & r3_lattice3(X0,sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

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

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k16_lattice3(X0,X2) != X1
          & r3_lattice3(X0,X1,X2)
          & r2_hidden(X1,X2) )
     => ( k16_lattice3(X0,sK8) != X1
        & r3_lattice3(X0,X1,sK8)
        & r2_hidden(X1,sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k16_lattice3(X0,X2) != sK7
            & r3_lattice3(X0,sK7,X2)
            & r2_hidden(sK7,X2) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK6,X2) != X1
              & r3_lattice3(sK6,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l3_lattices(sK6)
      & v4_lattice3(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k16_lattice3(sK6,sK8) != sK7
    & r3_lattice3(sK6,sK7,sK8)
    & r2_hidden(sK7,sK8)
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l3_lattices(sK6)
    & v4_lattice3(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f54,f53,f52])).

fof(f90,plain,(
    r3_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f55])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
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

fof(f66,plain,(
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

fof(f88,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f55])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f68,plain,(
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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,(
    r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    k16_lattice3(sK6,sK8) != sK7 ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | r3_lattice3(X0,sK5(X0,X1,X2),X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattices(X0,sK5(X0,X1,X2),X1)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_329,plain,
    ( ~ r3_lattice3(X0_52,X0_53,X0_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | m1_subset_1(sK5(X0_52,X0_53,X0_55),u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | k16_lattice3(X0_52,X0_55) = X0_53 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_970,plain,
    ( k16_lattice3(X0_52,X0_55) = X0_53
    | r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(sK5(X0_52,X0_53,X0_55),u1_struct_0(X0_52)) = iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_13,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_339,plain,
    ( ~ r3_lattice3(X0_52,X0_53,X0_55)
    | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_960,plain,
    ( r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_29,negated_conjecture,
    ( r3_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_323,negated_conjecture,
    ( r3_lattice3(sK6,sK7,sK8) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_975,plain,
    ( r3_lattice3(sK6,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_5,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_347,plain,
    ( r4_lattice3(X0_52,X0_53,X0_55)
    | r2_hidden(sK1(X0_52,X0_53,X0_55),X0_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_952,plain,
    ( r4_lattice3(X0_52,X0_53,X0_55) = iProver_top
    | r2_hidden(sK1(X0_52,X0_53,X0_55),X0_55) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | sK3(X0_53,X0_52,X0_55) = X0_53 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_962,plain,
    ( sK3(X0_53,X0_52,X0_55) = X0_53
    | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_1883,plain,
    ( sK3(sK1(X0_52,X0_53,a_2_1_lattice3(X1_52,X0_55)),X1_52,X0_55) = sK1(X0_52,X0_53,a_2_1_lattice3(X1_52,X0_55))
    | r4_lattice3(X0_52,X0_53,a_2_1_lattice3(X1_52,X0_55)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top
    | l3_lattices(X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_962])).

cnf(c_9,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_343,plain,
    ( ~ r4_lattice3(X0_52,X0_53,X0_55)
    | r4_lattice3(X0_52,sK2(X0_52,X0_55,X0_53),X0_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | k15_lattice3(X0_52,X0_55) = X0_53 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_956,plain,
    ( k15_lattice3(X0_52,X0_55) = X0_53
    | r4_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | r4_lattice3(X0_52,sK2(X0_52,X0_55,X0_53),X0_55) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_10,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_342,plain,
    ( ~ r4_lattice3(X0_52,X0_53,X0_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | m1_subset_1(sK2(X0_52,X0_55,X0_53),u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | k15_lattice3(X0_52,X0_55) = X0_53 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_957,plain,
    ( k15_lattice3(X0_52,X0_55) = X0_53
    | r4_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(sK2(X0_52,X0_55,X0_53),u1_struct_0(X0_52)) = iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_321,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_977,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_7,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_345,plain,
    ( ~ r4_lattice3(X0_52,X0_53,X0_55)
    | r1_lattices(X0_52,X1_53,X0_53)
    | ~ r2_hidden(X1_53,X0_55)
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_954,plain,
    ( r4_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | r1_lattices(X0_52,X1_53,X0_53) = iProver_top
    | r2_hidden(X1_53,X0_55) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_3679,plain,
    ( r4_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r1_lattices(sK6,sK7,X0_53) = iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_954])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_36,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( l3_lattices(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4076,plain,
    ( r4_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r1_lattices(sK6,sK7,X0_53) = iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3679,c_36,c_39])).

cnf(c_4906,plain,
    ( k15_lattice3(sK6,X0_55) = X0_53
    | r4_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r4_lattice3(sK6,sK2(sK6,X0_55,X0_53),X1_55) != iProver_top
    | r1_lattices(sK6,sK7,sK2(sK6,X0_55,X0_53)) = iProver_top
    | r2_hidden(sK7,X1_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
    | v10_lattices(sK6) != iProver_top
    | v4_lattice3(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_4076])).

cnf(c_34,negated_conjecture,
    ( v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,plain,
    ( v10_lattices(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_38,plain,
    ( v4_lattice3(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5527,plain,
    ( k15_lattice3(sK6,X0_55) = X0_53
    | r4_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r4_lattice3(sK6,sK2(sK6,X0_55,X0_53),X1_55) != iProver_top
    | r1_lattices(sK6,sK7,sK2(sK6,X0_55,X0_53)) = iProver_top
    | r2_hidden(sK7,X1_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4906,c_36,c_37,c_38,c_39])).

cnf(c_5539,plain,
    ( k15_lattice3(sK6,X0_55) = X0_53
    | r4_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r1_lattices(sK6,sK7,sK2(sK6,X0_55,X0_53)) = iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
    | v10_lattices(sK6) != iProver_top
    | v4_lattice3(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_5527])).

cnf(c_5818,plain,
    ( k15_lattice3(sK6,X0_55) = X0_53
    | r4_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r1_lattices(sK6,sK7,sK2(sK6,X0_55,X0_53)) = iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5539,c_36,c_37,c_38,c_39])).

cnf(c_8,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_344,plain,
    ( ~ r4_lattice3(X0_52,X0_53,X0_55)
    | ~ r1_lattices(X0_52,X0_53,sK2(X0_52,X0_55,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | k15_lattice3(X0_52,X0_55) = X0_53 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_955,plain,
    ( k15_lattice3(X0_52,X0_55) = X0_53
    | r4_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | r1_lattices(X0_52,X0_53,sK2(X0_52,X0_55,X0_53)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_5829,plain,
    ( k15_lattice3(sK6,X0_55) = sK7
    | r4_lattice3(sK6,sK7,X0_55) != iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v10_lattices(sK6) != iProver_top
    | v4_lattice3(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5818,c_955])).

cnf(c_40,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6018,plain,
    ( r2_hidden(sK7,X0_55) != iProver_top
    | r4_lattice3(sK6,sK7,X0_55) != iProver_top
    | k15_lattice3(sK6,X0_55) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5829,c_36,c_37,c_38,c_39,c_40])).

cnf(c_6019,plain,
    ( k15_lattice3(sK6,X0_55) = sK7
    | r4_lattice3(sK6,sK7,X0_55) != iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_6018])).

cnf(c_7027,plain,
    ( sK3(sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55)),X0_52,X0_55) = sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55))
    | k15_lattice3(sK6,a_2_1_lattice3(X0_52,X0_55)) = sK7
    | r2_hidden(sK7,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(X0_52) != iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_6019])).

cnf(c_44984,plain,
    ( l3_lattices(X0_52) != iProver_top
    | r2_hidden(sK7,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
    | k15_lattice3(sK6,a_2_1_lattice3(X0_52,X0_55)) = sK7
    | sK3(sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55)),X0_52,X0_55) = sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55))
    | v2_struct_0(X0_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7027,c_36,c_39,c_40])).

cnf(c_44985,plain,
    ( sK3(sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55)),X0_52,X0_55) = sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55))
    | k15_lattice3(sK6,a_2_1_lattice3(X0_52,X0_55)) = sK7
    | r2_hidden(sK7,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_44984])).

cnf(c_44995,plain,
    ( sK3(sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55)),X0_52,X0_55) = sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55))
    | k15_lattice3(sK6,a_2_1_lattice3(X0_52,X0_55)) = sK7
    | r3_lattice3(X0_52,sK7,X0_55) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_44985])).

cnf(c_45484,plain,
    ( sK3(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK6,sK8) = sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8))
    | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_44995])).

cnf(c_45588,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l3_lattices(sK6)
    | sK3(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK6,sK8) = sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8))
    | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45484])).

cnf(c_45605,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | sK3(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK6,sK8) = sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45484,c_35,c_32,c_31,c_45588])).

cnf(c_45606,plain,
    ( sK3(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK6,sK8) = sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8))
    | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
    inference(renaming,[status(thm)],[c_45605])).

cnf(c_14,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_338,plain,
    ( r3_lattice3(X0_52,sK3(X0_53,X0_52,X0_55),X0_55)
    | ~ r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_961,plain,
    ( r3_lattice3(X0_52,sK3(X0_53,X0_52,X0_55),X0_55) = iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55))
    | m1_subset_1(sK3(X0_53,X0_52,X0_55),u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_963,plain,
    ( r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
    | m1_subset_1(sK3(X0_53,X0_52,X0_55),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_3,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_349,plain,
    ( r1_lattices(X0_52,X0_53,X1_53)
    | ~ r3_lattice3(X0_52,X0_53,X0_55)
    | ~ r2_hidden(X1_53,X0_55)
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_950,plain,
    ( r1_lattices(X0_52,X0_53,X1_53) = iProver_top
    | r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | r2_hidden(X1_53,X0_55) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_2326,plain,
    ( r1_lattices(sK6,X0_53,sK7) = iProver_top
    | r3_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_950])).

cnf(c_2898,plain,
    ( r1_lattices(sK6,X0_53,sK7) = iProver_top
    | r3_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2326,c_36,c_39])).

cnf(c_2910,plain,
    ( r1_lattices(sK6,sK3(X0_53,sK6,X0_55),sK7) = iProver_top
    | r3_lattice3(sK6,sK3(X0_53,sK6,X0_55),X1_55) != iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(sK6,X0_55)) != iProver_top
    | r2_hidden(sK7,X1_55) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_2898])).

cnf(c_3173,plain,
    ( r1_lattices(sK6,sK3(X0_53,sK6,X0_55),sK7) = iProver_top
    | r3_lattice3(sK6,sK3(X0_53,sK6,X0_55),X1_55) != iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(sK6,X0_55)) != iProver_top
    | r2_hidden(sK7,X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2910,c_36,c_39])).

cnf(c_3183,plain,
    ( r1_lattices(sK6,sK3(X0_53,sK6,X0_55),sK7) = iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(sK6,X0_55)) != iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_3173])).

cnf(c_3426,plain,
    ( r1_lattices(sK6,sK3(X0_53,sK6,X0_55),sK7) = iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(sK6,X0_55)) != iProver_top
    | r2_hidden(sK7,X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3183,c_36,c_39])).

cnf(c_45615,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
    | r2_hidden(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),a_2_1_lattice3(sK6,sK8)) != iProver_top
    | r2_hidden(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_45606,c_3426])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,plain,
    ( r2_hidden(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_45917,plain,
    ( r2_hidden(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),a_2_1_lattice3(sK6,sK8)) != iProver_top
    | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
    | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45615,c_41])).

cnf(c_45918,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
    | r2_hidden(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),a_2_1_lattice3(sK6,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_45917])).

cnf(c_45924,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
    | r3_lattice3(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK8) != iProver_top
    | m1_subset_1(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_45918])).

cnf(c_42,plain,
    ( r3_lattice3(sK6,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_403,plain,
    ( r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_405,plain,
    ( r3_lattice3(sK6,sK7,sK8) != iProver_top
    | r2_hidden(sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_45925,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
    | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_45918])).

cnf(c_47213,plain,
    ( r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
    | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
    | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45925,c_36,c_39,c_40])).

cnf(c_47214,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
    | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_47213])).

cnf(c_4,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_348,plain,
    ( r4_lattice3(X0_52,X0_53,X0_55)
    | ~ r1_lattices(X0_52,sK1(X0_52,X0_53,X0_55),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_951,plain,
    ( r4_lattice3(X0_52,X0_53,X0_55) = iProver_top
    | r1_lattices(X0_52,sK1(X0_52,X0_53,X0_55),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_47220,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_47214,c_951])).

cnf(c_47459,plain,
    ( r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
    | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_47220,c_36,c_39,c_40])).

cnf(c_47460,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_47459])).

cnf(c_47471,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
    | r2_hidden(sK7,a_2_1_lattice3(sK6,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_47460,c_6019])).

cnf(c_49110,plain,
    ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45924,c_36,c_39,c_40,c_42,c_405,c_47471])).

cnf(c_27,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_325,plain,
    ( r3_lattices(X0_52,X0_53,k15_lattice3(X0_52,X0_55))
    | ~ r2_hidden(X0_53,X0_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_974,plain,
    ( r3_lattices(X0_52,X0_53,k15_lattice3(X0_52,X0_55)) = iProver_top
    | r2_hidden(X0_53,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_49116,plain,
    ( r3_lattices(sK6,X0_53,sK7) = iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(sK6,sK8)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
    | v10_lattices(sK6) != iProver_top
    | v4_lattice3(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_49110,c_974])).

cnf(c_49395,plain,
    ( r3_lattices(sK6,X0_53,sK7) = iProver_top
    | r2_hidden(X0_53,a_2_1_lattice3(sK6,sK8)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49116,c_36,c_37,c_38,c_39])).

cnf(c_49404,plain,
    ( r3_lattices(sK6,X0_53,sK7) = iProver_top
    | r3_lattice3(sK6,X0_53,sK8) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_49395])).

cnf(c_49451,plain,
    ( r3_lattices(sK6,X0_53,sK7) = iProver_top
    | r3_lattice3(sK6,X0_53,sK8) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49404,c_36,c_39])).

cnf(c_49461,plain,
    ( k16_lattice3(sK6,X0_55) = X0_53
    | r3_lattices(sK6,sK5(sK6,X0_53,X0_55),sK7) = iProver_top
    | r3_lattice3(sK6,X0_53,X0_55) != iProver_top
    | r3_lattice3(sK6,sK5(sK6,X0_53,X0_55),sK8) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
    | v10_lattices(sK6) != iProver_top
    | v4_lattice3(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_970,c_49451])).

cnf(c_49580,plain,
    ( k16_lattice3(sK6,sK8) = sK7
    | r3_lattices(sK6,sK5(sK6,sK7,sK8),sK7) = iProver_top
    | r3_lattice3(sK6,sK5(sK6,sK7,sK8),sK8) != iProver_top
    | r3_lattice3(sK6,sK7,sK8) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v10_lattices(sK6) != iProver_top
    | v4_lattice3(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49461])).

cnf(c_28,negated_conjecture,
    ( k16_lattice3(sK6,sK8) != sK7 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_324,negated_conjecture,
    ( k16_lattice3(sK6,sK8) != sK7 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_22,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK5(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_330,plain,
    ( ~ r3_lattice3(X0_52,X0_53,X0_55)
    | r3_lattice3(X0_52,sK5(X0_52,X0_53,X0_55),X0_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | k16_lattice3(X0_52,X0_55) = X0_53 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_430,plain,
    ( k16_lattice3(X0_52,X0_55) = X0_53
    | r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | r3_lattice3(X0_52,sK5(X0_52,X0_53,X0_55),X0_55) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_432,plain,
    ( k16_lattice3(sK6,sK8) = sK7
    | r3_lattice3(sK6,sK5(sK6,sK7,sK8),sK8) = iProver_top
    | r3_lattice3(sK6,sK7,sK8) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v10_lattices(sK6) != iProver_top
    | v4_lattice3(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_21,plain,
    ( ~ r3_lattices(X0,sK5(X0,X1,X2),X1)
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_331,plain,
    ( ~ r3_lattices(X0_52,sK5(X0_52,X0_53,X0_55),X0_53)
    | ~ r3_lattice3(X0_52,X0_53,X0_55)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | k16_lattice3(X0_52,X0_55) = X0_53 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_427,plain,
    ( k16_lattice3(X0_52,X0_55) = X0_53
    | r3_lattices(X0_52,sK5(X0_52,X0_53,X0_55),X0_53) != iProver_top
    | r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_429,plain,
    ( k16_lattice3(sK6,sK8) = sK7
    | r3_lattices(sK6,sK5(sK6,sK7,sK8),sK7) != iProver_top
    | r3_lattice3(sK6,sK7,sK8) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v10_lattices(sK6) != iProver_top
    | v4_lattice3(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49580,c_324,c_432,c_429,c_42,c_40,c_39,c_38,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.47/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.47/2.49  
% 15.47/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.47/2.49  
% 15.47/2.49  ------  iProver source info
% 15.47/2.49  
% 15.47/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.47/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.47/2.49  git: non_committed_changes: false
% 15.47/2.49  git: last_make_outside_of_git: false
% 15.47/2.49  
% 15.47/2.49  ------ 
% 15.47/2.49  ------ Parsing...
% 15.47/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.47/2.49  
% 15.47/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.47/2.49  
% 15.47/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.47/2.49  
% 15.47/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.47/2.49  ------ Proving...
% 15.47/2.49  ------ Problem Properties 
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  clauses                                 36
% 15.47/2.49  conjectures                             8
% 15.47/2.49  EPR                                     6
% 15.47/2.49  Horn                                    8
% 15.47/2.49  unary                                   8
% 15.47/2.49  binary                                  0
% 15.47/2.49  lits                                    184
% 15.47/2.49  lits eq                                 9
% 15.47/2.49  fd_pure                                 0
% 15.47/2.49  fd_pseudo                               0
% 15.47/2.49  fd_cond                                 0
% 15.47/2.49  fd_pseudo_cond                          6
% 15.47/2.49  AC symbols                              0
% 15.47/2.49  
% 15.47/2.49  ------ Input Options Time Limit: Unbounded
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  ------ 
% 15.47/2.49  Current options:
% 15.47/2.49  ------ 
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  ------ Proving...
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  % SZS status Theorem for theBenchmark.p
% 15.47/2.49  
% 15.47/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.47/2.49  
% 15.47/2.49  fof(f6,axiom,(
% 15.47/2.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 15.47/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.49  
% 15.47/2.49  fof(f20,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 15.47/2.49    inference(ennf_transformation,[],[f6])).
% 15.47/2.49  
% 15.47/2.49  fof(f21,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(flattening,[],[f20])).
% 15.47/2.49  
% 15.47/2.49  fof(f47,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(nnf_transformation,[],[f21])).
% 15.47/2.49  
% 15.47/2.49  fof(f48,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(flattening,[],[f47])).
% 15.47/2.49  
% 15.47/2.49  fof(f49,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(rectify,[],[f48])).
% 15.47/2.49  
% 15.47/2.49  fof(f50,plain,(
% 15.47/2.49    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK5(X0,X1,X2),X1) & r3_lattice3(X0,sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 15.47/2.49    introduced(choice_axiom,[])).
% 15.47/2.49  
% 15.47/2.49  fof(f51,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK5(X0,X1,X2),X1) & r3_lattice3(X0,sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 15.47/2.49  
% 15.47/2.49  fof(f79,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f51])).
% 15.47/2.49  
% 15.47/2.49  fof(f4,axiom,(
% 15.47/2.49    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 15.47/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.49  
% 15.47/2.49  fof(f16,plain,(
% 15.47/2.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 15.47/2.49    inference(ennf_transformation,[],[f4])).
% 15.47/2.49  
% 15.47/2.49  fof(f17,plain,(
% 15.47/2.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 15.47/2.49    inference(flattening,[],[f16])).
% 15.47/2.49  
% 15.47/2.49  fof(f39,plain,(
% 15.47/2.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 15.47/2.49    inference(nnf_transformation,[],[f17])).
% 15.47/2.49  
% 15.47/2.49  fof(f40,plain,(
% 15.47/2.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 15.47/2.49    inference(rectify,[],[f39])).
% 15.47/2.49  
% 15.47/2.49  fof(f41,plain,(
% 15.47/2.49    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 15.47/2.49    introduced(choice_axiom,[])).
% 15.47/2.49  
% 15.47/2.49  fof(f42,plain,(
% 15.47/2.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 15.47/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 15.47/2.49  
% 15.47/2.49  fof(f72,plain,(
% 15.47/2.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f42])).
% 15.47/2.49  
% 15.47/2.49  fof(f94,plain,(
% 15.47/2.49    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 15.47/2.49    inference(equality_resolution,[],[f72])).
% 15.47/2.49  
% 15.47/2.49  fof(f8,conjecture,(
% 15.47/2.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 15.47/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.49  
% 15.47/2.49  fof(f9,negated_conjecture,(
% 15.47/2.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 15.47/2.49    inference(negated_conjecture,[],[f8])).
% 15.47/2.49  
% 15.47/2.49  fof(f24,plain,(
% 15.47/2.49    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 15.47/2.49    inference(ennf_transformation,[],[f9])).
% 15.47/2.49  
% 15.47/2.49  fof(f25,plain,(
% 15.47/2.49    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 15.47/2.49    inference(flattening,[],[f24])).
% 15.47/2.49  
% 15.47/2.49  fof(f54,plain,(
% 15.47/2.49    ( ! [X0,X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => (k16_lattice3(X0,sK8) != X1 & r3_lattice3(X0,X1,sK8) & r2_hidden(X1,sK8))) )),
% 15.47/2.49    introduced(choice_axiom,[])).
% 15.47/2.49  
% 15.47/2.49  fof(f53,plain,(
% 15.47/2.49    ( ! [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k16_lattice3(X0,X2) != sK7 & r3_lattice3(X0,sK7,X2) & r2_hidden(sK7,X2)) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 15.47/2.49    introduced(choice_axiom,[])).
% 15.47/2.49  
% 15.47/2.49  fof(f52,plain,(
% 15.47/2.49    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK6,X2) != X1 & r3_lattice3(sK6,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK6))) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6))),
% 15.47/2.49    introduced(choice_axiom,[])).
% 15.47/2.49  
% 15.47/2.49  fof(f55,plain,(
% 15.47/2.49    ((k16_lattice3(sK6,sK8) != sK7 & r3_lattice3(sK6,sK7,sK8) & r2_hidden(sK7,sK8)) & m1_subset_1(sK7,u1_struct_0(sK6))) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6)),
% 15.47/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f54,f53,f52])).
% 15.47/2.49  
% 15.47/2.49  fof(f90,plain,(
% 15.47/2.49    r3_lattice3(sK6,sK7,sK8)),
% 15.47/2.49    inference(cnf_transformation,[],[f55])).
% 15.47/2.49  
% 15.47/2.49  fof(f2,axiom,(
% 15.47/2.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 15.47/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.49  
% 15.47/2.49  fof(f12,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.47/2.49    inference(ennf_transformation,[],[f2])).
% 15.47/2.49  
% 15.47/2.49  fof(f13,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(flattening,[],[f12])).
% 15.47/2.49  
% 15.47/2.49  fof(f30,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(nnf_transformation,[],[f13])).
% 15.47/2.49  
% 15.47/2.49  fof(f31,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(rectify,[],[f30])).
% 15.47/2.49  
% 15.47/2.49  fof(f32,plain,(
% 15.47/2.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 15.47/2.49    introduced(choice_axiom,[])).
% 15.47/2.49  
% 15.47/2.49  fof(f33,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 15.47/2.49  
% 15.47/2.49  fof(f62,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f33])).
% 15.47/2.49  
% 15.47/2.49  fof(f70,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f42])).
% 15.47/2.49  
% 15.47/2.49  fof(f3,axiom,(
% 15.47/2.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 15.47/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.49  
% 15.47/2.49  fof(f14,plain,(
% 15.47/2.49    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.47/2.49    inference(ennf_transformation,[],[f3])).
% 15.47/2.49  
% 15.47/2.49  fof(f15,plain,(
% 15.47/2.49    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(flattening,[],[f14])).
% 15.47/2.49  
% 15.47/2.49  fof(f34,plain,(
% 15.47/2.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(nnf_transformation,[],[f15])).
% 15.47/2.49  
% 15.47/2.49  fof(f35,plain,(
% 15.47/2.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(flattening,[],[f34])).
% 15.47/2.49  
% 15.47/2.49  fof(f36,plain,(
% 15.47/2.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(rectify,[],[f35])).
% 15.47/2.49  
% 15.47/2.49  fof(f37,plain,(
% 15.47/2.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 15.47/2.49    introduced(choice_axiom,[])).
% 15.47/2.49  
% 15.47/2.49  fof(f38,plain,(
% 15.47/2.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 15.47/2.49  
% 15.47/2.49  fof(f67,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK2(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f38])).
% 15.47/2.49  
% 15.47/2.49  fof(f66,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f38])).
% 15.47/2.49  
% 15.47/2.49  fof(f88,plain,(
% 15.47/2.49    m1_subset_1(sK7,u1_struct_0(sK6))),
% 15.47/2.49    inference(cnf_transformation,[],[f55])).
% 15.47/2.49  
% 15.47/2.49  fof(f60,plain,(
% 15.47/2.49    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f33])).
% 15.47/2.49  
% 15.47/2.49  fof(f84,plain,(
% 15.47/2.49    ~v2_struct_0(sK6)),
% 15.47/2.49    inference(cnf_transformation,[],[f55])).
% 15.47/2.49  
% 15.47/2.49  fof(f87,plain,(
% 15.47/2.49    l3_lattices(sK6)),
% 15.47/2.49    inference(cnf_transformation,[],[f55])).
% 15.47/2.49  
% 15.47/2.49  fof(f85,plain,(
% 15.47/2.49    v10_lattices(sK6)),
% 15.47/2.49    inference(cnf_transformation,[],[f55])).
% 15.47/2.49  
% 15.47/2.49  fof(f86,plain,(
% 15.47/2.49    v4_lattice3(sK6)),
% 15.47/2.49    inference(cnf_transformation,[],[f55])).
% 15.47/2.49  
% 15.47/2.49  fof(f68,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK2(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f38])).
% 15.47/2.49  
% 15.47/2.49  fof(f71,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK3(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f42])).
% 15.47/2.49  
% 15.47/2.49  fof(f69,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f42])).
% 15.47/2.49  
% 15.47/2.49  fof(f1,axiom,(
% 15.47/2.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 15.47/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.49  
% 15.47/2.49  fof(f10,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.47/2.49    inference(ennf_transformation,[],[f1])).
% 15.47/2.49  
% 15.47/2.49  fof(f11,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(flattening,[],[f10])).
% 15.47/2.49  
% 15.47/2.49  fof(f26,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(nnf_transformation,[],[f11])).
% 15.47/2.49  
% 15.47/2.49  fof(f27,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(rectify,[],[f26])).
% 15.47/2.49  
% 15.47/2.49  fof(f28,plain,(
% 15.47/2.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 15.47/2.49    introduced(choice_axiom,[])).
% 15.47/2.49  
% 15.47/2.49  fof(f29,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 15.47/2.49  
% 15.47/2.49  fof(f56,plain,(
% 15.47/2.49    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f29])).
% 15.47/2.49  
% 15.47/2.49  fof(f89,plain,(
% 15.47/2.49    r2_hidden(sK7,sK8)),
% 15.47/2.49    inference(cnf_transformation,[],[f55])).
% 15.47/2.49  
% 15.47/2.49  fof(f63,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f33])).
% 15.47/2.49  
% 15.47/2.49  fof(f7,axiom,(
% 15.47/2.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 15.47/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.47/2.49  
% 15.47/2.49  fof(f22,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 15.47/2.49    inference(ennf_transformation,[],[f7])).
% 15.47/2.49  
% 15.47/2.49  fof(f23,plain,(
% 15.47/2.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.47/2.49    inference(flattening,[],[f22])).
% 15.47/2.49  
% 15.47/2.49  fof(f82,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f23])).
% 15.47/2.49  
% 15.47/2.49  fof(f91,plain,(
% 15.47/2.49    k16_lattice3(sK6,sK8) != sK7),
% 15.47/2.49    inference(cnf_transformation,[],[f55])).
% 15.47/2.49  
% 15.47/2.49  fof(f80,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | r3_lattice3(X0,sK5(X0,X1,X2),X2) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f51])).
% 15.47/2.49  
% 15.47/2.49  fof(f81,plain,(
% 15.47/2.49    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | ~r3_lattices(X0,sK5(X0,X1,X2),X1) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.47/2.49    inference(cnf_transformation,[],[f51])).
% 15.47/2.49  
% 15.47/2.49  cnf(c_23,plain,
% 15.47/2.49      ( ~ r3_lattice3(X0,X1,X2)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
% 15.47/2.49      | ~ v10_lattices(X0)
% 15.47/2.49      | ~ v4_lattice3(X0)
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0)
% 15.47/2.49      | k16_lattice3(X0,X2) = X1 ),
% 15.47/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_329,plain,
% 15.47/2.49      ( ~ r3_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | m1_subset_1(sK5(X0_52,X0_53,X0_55),u1_struct_0(X0_52))
% 15.47/2.49      | ~ v10_lattices(X0_52)
% 15.47/2.49      | ~ v4_lattice3(X0_52)
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52)
% 15.47/2.49      | k16_lattice3(X0_52,X0_55) = X0_53 ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_23]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_970,plain,
% 15.47/2.49      ( k16_lattice3(X0_52,X0_55) = X0_53
% 15.47/2.49      | r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | m1_subset_1(sK5(X0_52,X0_53,X0_55),u1_struct_0(X0_52)) = iProver_top
% 15.47/2.49      | v10_lattices(X0_52) != iProver_top
% 15.47/2.49      | v4_lattice3(X0_52) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_13,plain,
% 15.47/2.49      ( ~ r3_lattice3(X0,X1,X2)
% 15.47/2.49      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0) ),
% 15.47/2.49      inference(cnf_transformation,[],[f94]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_339,plain,
% 15.47/2.49      ( ~ r3_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55))
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_13]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_960,plain,
% 15.47/2.49      ( r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) = iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_29,negated_conjecture,
% 15.47/2.49      ( r3_lattice3(sK6,sK7,sK8) ),
% 15.47/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_323,negated_conjecture,
% 15.47/2.49      ( r3_lattice3(sK6,sK7,sK8) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_29]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_975,plain,
% 15.47/2.49      ( r3_lattice3(sK6,sK7,sK8) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5,plain,
% 15.47/2.49      ( r4_lattice3(X0,X1,X2)
% 15.47/2.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0) ),
% 15.47/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_347,plain,
% 15.47/2.49      ( r4_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | r2_hidden(sK1(X0_52,X0_53,X0_55),X0_55)
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_5]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_952,plain,
% 15.47/2.49      ( r4_lattice3(X0_52,X0_53,X0_55) = iProver_top
% 15.47/2.49      | r2_hidden(sK1(X0_52,X0_53,X0_55),X0_55) = iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_15,plain,
% 15.47/2.49      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 15.47/2.49      | v2_struct_0(X1)
% 15.47/2.49      | ~ l3_lattices(X1)
% 15.47/2.49      | sK3(X0,X1,X2) = X0 ),
% 15.47/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_337,plain,
% 15.47/2.49      ( ~ r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55))
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52)
% 15.47/2.49      | sK3(X0_53,X0_52,X0_55) = X0_53 ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_15]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_962,plain,
% 15.47/2.49      ( sK3(X0_53,X0_52,X0_55) = X0_53
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_1883,plain,
% 15.47/2.49      ( sK3(sK1(X0_52,X0_53,a_2_1_lattice3(X1_52,X0_55)),X1_52,X0_55) = sK1(X0_52,X0_53,a_2_1_lattice3(X1_52,X0_55))
% 15.47/2.49      | r4_lattice3(X0_52,X0_53,a_2_1_lattice3(X1_52,X0_55)) = iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | v2_struct_0(X1_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top
% 15.47/2.49      | l3_lattices(X1_52) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_952,c_962]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_9,plain,
% 15.47/2.49      ( ~ r4_lattice3(X0,X1,X2)
% 15.47/2.49      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | ~ v10_lattices(X0)
% 15.47/2.49      | ~ v4_lattice3(X0)
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0)
% 15.47/2.49      | k15_lattice3(X0,X2) = X1 ),
% 15.47/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_343,plain,
% 15.47/2.49      ( ~ r4_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | r4_lattice3(X0_52,sK2(X0_52,X0_55,X0_53),X0_55)
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | ~ v10_lattices(X0_52)
% 15.47/2.49      | ~ v4_lattice3(X0_52)
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52)
% 15.47/2.49      | k15_lattice3(X0_52,X0_55) = X0_53 ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_9]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_956,plain,
% 15.47/2.49      ( k15_lattice3(X0_52,X0_55) = X0_53
% 15.47/2.49      | r4_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r4_lattice3(X0_52,sK2(X0_52,X0_55,X0_53),X0_55) = iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v10_lattices(X0_52) != iProver_top
% 15.47/2.49      | v4_lattice3(X0_52) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_10,plain,
% 15.47/2.49      ( ~ r4_lattice3(X0,X1,X2)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 15.47/2.49      | ~ v10_lattices(X0)
% 15.47/2.49      | ~ v4_lattice3(X0)
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0)
% 15.47/2.49      | k15_lattice3(X0,X2) = X1 ),
% 15.47/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_342,plain,
% 15.47/2.49      ( ~ r4_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | m1_subset_1(sK2(X0_52,X0_55,X0_53),u1_struct_0(X0_52))
% 15.47/2.49      | ~ v10_lattices(X0_52)
% 15.47/2.49      | ~ v4_lattice3(X0_52)
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52)
% 15.47/2.49      | k15_lattice3(X0_52,X0_55) = X0_53 ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_10]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_957,plain,
% 15.47/2.49      ( k15_lattice3(X0_52,X0_55) = X0_53
% 15.47/2.49      | r4_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | m1_subset_1(sK2(X0_52,X0_55,X0_53),u1_struct_0(X0_52)) = iProver_top
% 15.47/2.49      | v10_lattices(X0_52) != iProver_top
% 15.47/2.49      | v4_lattice3(X0_52) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_31,negated_conjecture,
% 15.47/2.49      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 15.47/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_321,negated_conjecture,
% 15.47/2.49      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_31]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_977,plain,
% 15.47/2.49      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_7,plain,
% 15.47/2.49      ( ~ r4_lattice3(X0,X1,X2)
% 15.47/2.49      | r1_lattices(X0,X3,X1)
% 15.47/2.49      | ~ r2_hidden(X3,X2)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0) ),
% 15.47/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_345,plain,
% 15.47/2.49      ( ~ r4_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | r1_lattices(X0_52,X1_53,X0_53)
% 15.47/2.49      | ~ r2_hidden(X1_53,X0_55)
% 15.47/2.49      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_7]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_954,plain,
% 15.47/2.49      ( r4_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r1_lattices(X0_52,X1_53,X0_53) = iProver_top
% 15.47/2.49      | r2_hidden(X1_53,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X1_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3679,plain,
% 15.47/2.49      ( r4_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK7,X0_53) = iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_977,c_954]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_35,negated_conjecture,
% 15.47/2.49      ( ~ v2_struct_0(sK6) ),
% 15.47/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_36,plain,
% 15.47/2.49      ( v2_struct_0(sK6) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_32,negated_conjecture,
% 15.47/2.49      ( l3_lattices(sK6) ),
% 15.47/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_39,plain,
% 15.47/2.49      ( l3_lattices(sK6) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_4076,plain,
% 15.47/2.49      ( r4_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK7,X0_53) = iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_3679,c_36,c_39]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_4906,plain,
% 15.47/2.49      ( k15_lattice3(sK6,X0_55) = X0_53
% 15.47/2.49      | r4_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r4_lattice3(sK6,sK2(sK6,X0_55,X0_53),X1_55) != iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK7,sK2(sK6,X0_55,X0_53)) = iProver_top
% 15.47/2.49      | r2_hidden(sK7,X1_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v10_lattices(sK6) != iProver_top
% 15.47/2.49      | v4_lattice3(sK6) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_957,c_4076]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_34,negated_conjecture,
% 15.47/2.49      ( v10_lattices(sK6) ),
% 15.47/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_37,plain,
% 15.47/2.49      ( v10_lattices(sK6) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_33,negated_conjecture,
% 15.47/2.49      ( v4_lattice3(sK6) ),
% 15.47/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_38,plain,
% 15.47/2.49      ( v4_lattice3(sK6) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5527,plain,
% 15.47/2.49      ( k15_lattice3(sK6,X0_55) = X0_53
% 15.47/2.49      | r4_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r4_lattice3(sK6,sK2(sK6,X0_55,X0_53),X1_55) != iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK7,sK2(sK6,X0_55,X0_53)) = iProver_top
% 15.47/2.49      | r2_hidden(sK7,X1_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_4906,c_36,c_37,c_38,c_39]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5539,plain,
% 15.47/2.49      ( k15_lattice3(sK6,X0_55) = X0_53
% 15.47/2.49      | r4_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK7,sK2(sK6,X0_55,X0_53)) = iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v10_lattices(sK6) != iProver_top
% 15.47/2.49      | v4_lattice3(sK6) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_956,c_5527]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5818,plain,
% 15.47/2.49      ( k15_lattice3(sK6,X0_55) = X0_53
% 15.47/2.49      | r4_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK7,sK2(sK6,X0_55,X0_53)) = iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_5539,c_36,c_37,c_38,c_39]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_8,plain,
% 15.47/2.49      ( ~ r4_lattice3(X0,X1,X2)
% 15.47/2.49      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | ~ v10_lattices(X0)
% 15.47/2.49      | ~ v4_lattice3(X0)
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0)
% 15.47/2.49      | k15_lattice3(X0,X2) = X1 ),
% 15.47/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_344,plain,
% 15.47/2.49      ( ~ r4_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | ~ r1_lattices(X0_52,X0_53,sK2(X0_52,X0_55,X0_53))
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | ~ v10_lattices(X0_52)
% 15.47/2.49      | ~ v4_lattice3(X0_52)
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52)
% 15.47/2.49      | k15_lattice3(X0_52,X0_55) = X0_53 ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_8]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_955,plain,
% 15.47/2.49      ( k15_lattice3(X0_52,X0_55) = X0_53
% 15.47/2.49      | r4_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r1_lattices(X0_52,X0_53,sK2(X0_52,X0_55,X0_53)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v10_lattices(X0_52) != iProver_top
% 15.47/2.49      | v4_lattice3(X0_52) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_5829,plain,
% 15.47/2.49      ( k15_lattice3(sK6,X0_55) = sK7
% 15.47/2.49      | r4_lattice3(sK6,sK7,X0_55) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v10_lattices(sK6) != iProver_top
% 15.47/2.49      | v4_lattice3(sK6) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_5818,c_955]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_40,plain,
% 15.47/2.49      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_6018,plain,
% 15.47/2.49      ( r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | r4_lattice3(sK6,sK7,X0_55) != iProver_top
% 15.47/2.49      | k15_lattice3(sK6,X0_55) = sK7 ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_5829,c_36,c_37,c_38,c_39,c_40]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_6019,plain,
% 15.47/2.49      ( k15_lattice3(sK6,X0_55) = sK7
% 15.47/2.49      | r4_lattice3(sK6,sK7,X0_55) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_6018]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_7027,plain,
% 15.47/2.49      ( sK3(sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55)),X0_52,X0_55) = sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55))
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(X0_52,X0_55)) = sK7
% 15.47/2.49      | r2_hidden(sK7,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_1883,c_6019]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_44984,plain,
% 15.47/2.49      ( l3_lattices(X0_52) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(X0_52,X0_55)) = sK7
% 15.47/2.49      | sK3(sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55)),X0_52,X0_55) = sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55))
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_7027,c_36,c_39,c_40]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_44985,plain,
% 15.47/2.49      ( sK3(sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55)),X0_52,X0_55) = sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55))
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(X0_52,X0_55)) = sK7
% 15.47/2.49      | r2_hidden(sK7,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_44984]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_44995,plain,
% 15.47/2.49      ( sK3(sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55)),X0_52,X0_55) = sK1(sK6,sK7,a_2_1_lattice3(X0_52,X0_55))
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(X0_52,X0_55)) = sK7
% 15.47/2.49      | r3_lattice3(X0_52,sK7,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_960,c_44985]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45484,plain,
% 15.47/2.49      ( sK3(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK6,sK8) = sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8))
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_975,c_44995]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45588,plain,
% 15.47/2.49      ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 15.47/2.49      | v2_struct_0(sK6)
% 15.47/2.49      | ~ l3_lattices(sK6)
% 15.47/2.49      | sK3(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK6,sK8) = sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8))
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
% 15.47/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_45484]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45605,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | sK3(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK6,sK8) = sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)) ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_45484,c_35,c_32,c_31,c_45588]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45606,plain,
% 15.47/2.49      ( sK3(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK6,sK8) = sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8))
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_45605]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_14,plain,
% 15.47/2.49      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 15.47/2.49      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0) ),
% 15.47/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_338,plain,
% 15.47/2.49      ( r3_lattice3(X0_52,sK3(X0_53,X0_52,X0_55),X0_55)
% 15.47/2.49      | ~ r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55))
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_14]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_961,plain,
% 15.47/2.49      ( r3_lattice3(X0_52,sK3(X0_53,X0_52,X0_55),X0_55) = iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_16,plain,
% 15.47/2.49      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 15.47/2.49      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 15.47/2.49      | v2_struct_0(X1)
% 15.47/2.49      | ~ l3_lattices(X1) ),
% 15.47/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_336,plain,
% 15.47/2.49      ( ~ r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55))
% 15.47/2.49      | m1_subset_1(sK3(X0_53,X0_52,X0_55),u1_struct_0(X0_52))
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_16]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_963,plain,
% 15.47/2.49      ( r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) != iProver_top
% 15.47/2.49      | m1_subset_1(sK3(X0_53,X0_52,X0_55),u1_struct_0(X0_52)) = iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3,plain,
% 15.47/2.49      ( r1_lattices(X0,X1,X2)
% 15.47/2.49      | ~ r3_lattice3(X0,X1,X3)
% 15.47/2.49      | ~ r2_hidden(X2,X3)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0) ),
% 15.47/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_349,plain,
% 15.47/2.49      ( r1_lattices(X0_52,X0_53,X1_53)
% 15.47/2.49      | ~ r3_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | ~ r2_hidden(X1_53,X0_55)
% 15.47/2.49      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_3]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_950,plain,
% 15.47/2.49      ( r1_lattices(X0_52,X0_53,X1_53) = iProver_top
% 15.47/2.49      | r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r2_hidden(X1_53,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X1_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2326,plain,
% 15.47/2.49      ( r1_lattices(sK6,X0_53,sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_977,c_950]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2898,plain,
% 15.47/2.49      ( r1_lattices(sK6,X0_53,sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_2326,c_36,c_39]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_2910,plain,
% 15.47/2.49      ( r1_lattices(sK6,sK3(X0_53,sK6,X0_55),sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,sK3(X0_53,sK6,X0_55),X1_55) != iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(sK6,X0_55)) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,X1_55) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_963,c_2898]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3173,plain,
% 15.47/2.49      ( r1_lattices(sK6,sK3(X0_53,sK6,X0_55),sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,sK3(X0_53,sK6,X0_55),X1_55) != iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(sK6,X0_55)) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,X1_55) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_2910,c_36,c_39]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3183,plain,
% 15.47/2.49      ( r1_lattices(sK6,sK3(X0_53,sK6,X0_55),sK7) = iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(sK6,X0_55)) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_961,c_3173]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_3426,plain,
% 15.47/2.49      ( r1_lattices(sK6,sK3(X0_53,sK6,X0_55),sK7) = iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(sK6,X0_55)) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,X0_55) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_3183,c_36,c_39]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45615,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
% 15.47/2.49      | r2_hidden(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),a_2_1_lattice3(sK6,sK8)) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,sK8) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_45606,c_3426]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_30,negated_conjecture,
% 15.47/2.49      ( r2_hidden(sK7,sK8) ),
% 15.47/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_41,plain,
% 15.47/2.49      ( r2_hidden(sK7,sK8) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45917,plain,
% 15.47/2.49      ( r2_hidden(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),a_2_1_lattice3(sK6,sK8)) != iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_45615,c_41]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45918,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
% 15.47/2.49      | r2_hidden(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),a_2_1_lattice3(sK6,sK8)) != iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_45917]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45924,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK8) != iProver_top
% 15.47/2.49      | m1_subset_1(sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_960,c_45918]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_42,plain,
% 15.47/2.49      ( r3_lattice3(sK6,sK7,sK8) = iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_403,plain,
% 15.47/2.49      ( r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(X0_52,X0_55)) = iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_405,plain,
% 15.47/2.49      ( r3_lattice3(sK6,sK7,sK8) != iProver_top
% 15.47/2.49      | r2_hidden(sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(instantiation,[status(thm)],[c_403]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_45925,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_952,c_45918]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_47213,plain,
% 15.47/2.49      ( r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top
% 15.47/2.49      | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_45925,c_36,c_39,c_40]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_47214,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
% 15.47/2.49      | r1_lattices(sK6,sK1(sK6,sK7,a_2_1_lattice3(sK6,sK8)),sK7) = iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_47213]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_4,plain,
% 15.47/2.49      ( r4_lattice3(X0,X1,X2)
% 15.47/2.49      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0) ),
% 15.47/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_348,plain,
% 15.47/2.49      ( r4_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | ~ r1_lattices(X0_52,sK1(X0_52,X0_53,X0_55),X0_53)
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_4]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_951,plain,
% 15.47/2.49      ( r4_lattice3(X0_52,X0_53,X0_55) = iProver_top
% 15.47/2.49      | r1_lattices(X0_52,sK1(X0_52,X0_53,X0_55),X0_53) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_47220,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_47214,c_951]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_47459,plain,
% 15.47/2.49      ( r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top
% 15.47/2.49      | k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_47220,c_36,c_39,c_40]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_47460,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | r4_lattice3(sK6,sK7,a_2_1_lattice3(sK6,sK8)) = iProver_top ),
% 15.47/2.49      inference(renaming,[status(thm)],[c_47459]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_47471,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7
% 15.47/2.49      | r2_hidden(sK7,a_2_1_lattice3(sK6,sK8)) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_47460,c_6019]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_49110,plain,
% 15.47/2.49      ( k15_lattice3(sK6,a_2_1_lattice3(sK6,sK8)) = sK7 ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_45924,c_36,c_39,c_40,c_42,c_405,c_47471]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_27,plain,
% 15.47/2.49      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 15.47/2.49      | ~ r2_hidden(X1,X2)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | ~ v10_lattices(X0)
% 15.47/2.49      | ~ v4_lattice3(X0)
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0) ),
% 15.47/2.49      inference(cnf_transformation,[],[f82]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_325,plain,
% 15.47/2.49      ( r3_lattices(X0_52,X0_53,k15_lattice3(X0_52,X0_55))
% 15.47/2.49      | ~ r2_hidden(X0_53,X0_55)
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | ~ v10_lattices(X0_52)
% 15.47/2.49      | ~ v4_lattice3(X0_52)
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52) ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_27]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_974,plain,
% 15.47/2.49      ( r3_lattices(X0_52,X0_53,k15_lattice3(X0_52,X0_55)) = iProver_top
% 15.47/2.49      | r2_hidden(X0_53,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v10_lattices(X0_52) != iProver_top
% 15.47/2.49      | v4_lattice3(X0_52) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_49116,plain,
% 15.47/2.49      ( r3_lattices(sK6,X0_53,sK7) = iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(sK6,sK8)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v10_lattices(sK6) != iProver_top
% 15.47/2.49      | v4_lattice3(sK6) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_49110,c_974]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_49395,plain,
% 15.47/2.49      ( r3_lattices(sK6,X0_53,sK7) = iProver_top
% 15.47/2.49      | r2_hidden(X0_53,a_2_1_lattice3(sK6,sK8)) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_49116,c_36,c_37,c_38,c_39]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_49404,plain,
% 15.47/2.49      ( r3_lattices(sK6,X0_53,sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,X0_53,sK8) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_960,c_49395]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_49451,plain,
% 15.47/2.49      ( r3_lattices(sK6,X0_53,sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,X0_53,sK8) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top ),
% 15.47/2.49      inference(global_propositional_subsumption,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_49404,c_36,c_39]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_49461,plain,
% 15.47/2.49      ( k16_lattice3(sK6,X0_55) = X0_53
% 15.47/2.49      | r3_lattices(sK6,sK5(sK6,X0_53,X0_55),sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r3_lattice3(sK6,sK5(sK6,X0_53,X0_55),sK8) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v10_lattices(sK6) != iProver_top
% 15.47/2.49      | v4_lattice3(sK6) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(superposition,[status(thm)],[c_970,c_49451]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_49580,plain,
% 15.47/2.49      ( k16_lattice3(sK6,sK8) = sK7
% 15.47/2.49      | r3_lattices(sK6,sK5(sK6,sK7,sK8),sK7) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,sK5(sK6,sK7,sK8),sK8) != iProver_top
% 15.47/2.49      | r3_lattice3(sK6,sK7,sK8) != iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v10_lattices(sK6) != iProver_top
% 15.47/2.49      | v4_lattice3(sK6) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(instantiation,[status(thm)],[c_49461]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_28,negated_conjecture,
% 15.47/2.49      ( k16_lattice3(sK6,sK8) != sK7 ),
% 15.47/2.49      inference(cnf_transformation,[],[f91]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_324,negated_conjecture,
% 15.47/2.49      ( k16_lattice3(sK6,sK8) != sK7 ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_28]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_22,plain,
% 15.47/2.49      ( ~ r3_lattice3(X0,X1,X2)
% 15.47/2.49      | r3_lattice3(X0,sK5(X0,X1,X2),X2)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | ~ v10_lattices(X0)
% 15.47/2.49      | ~ v4_lattice3(X0)
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0)
% 15.47/2.49      | k16_lattice3(X0,X2) = X1 ),
% 15.47/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_330,plain,
% 15.47/2.49      ( ~ r3_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | r3_lattice3(X0_52,sK5(X0_52,X0_53,X0_55),X0_55)
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | ~ v10_lattices(X0_52)
% 15.47/2.49      | ~ v4_lattice3(X0_52)
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52)
% 15.47/2.49      | k16_lattice3(X0_52,X0_55) = X0_53 ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_22]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_430,plain,
% 15.47/2.49      ( k16_lattice3(X0_52,X0_55) = X0_53
% 15.47/2.49      | r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | r3_lattice3(X0_52,sK5(X0_52,X0_53,X0_55),X0_55) = iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v10_lattices(X0_52) != iProver_top
% 15.47/2.49      | v4_lattice3(X0_52) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_432,plain,
% 15.47/2.49      ( k16_lattice3(sK6,sK8) = sK7
% 15.47/2.49      | r3_lattice3(sK6,sK5(sK6,sK7,sK8),sK8) = iProver_top
% 15.47/2.49      | r3_lattice3(sK6,sK7,sK8) != iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v10_lattices(sK6) != iProver_top
% 15.47/2.49      | v4_lattice3(sK6) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(instantiation,[status(thm)],[c_430]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_21,plain,
% 15.47/2.49      ( ~ r3_lattices(X0,sK5(X0,X1,X2),X1)
% 15.47/2.49      | ~ r3_lattice3(X0,X1,X2)
% 15.47/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.49      | ~ v10_lattices(X0)
% 15.47/2.49      | ~ v4_lattice3(X0)
% 15.47/2.49      | v2_struct_0(X0)
% 15.47/2.49      | ~ l3_lattices(X0)
% 15.47/2.49      | k16_lattice3(X0,X2) = X1 ),
% 15.47/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_331,plain,
% 15.47/2.49      ( ~ r3_lattices(X0_52,sK5(X0_52,X0_53,X0_55),X0_53)
% 15.47/2.49      | ~ r3_lattice3(X0_52,X0_53,X0_55)
% 15.47/2.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 15.47/2.49      | ~ v10_lattices(X0_52)
% 15.47/2.49      | ~ v4_lattice3(X0_52)
% 15.47/2.49      | v2_struct_0(X0_52)
% 15.47/2.49      | ~ l3_lattices(X0_52)
% 15.47/2.49      | k16_lattice3(X0_52,X0_55) = X0_53 ),
% 15.47/2.49      inference(subtyping,[status(esa)],[c_21]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_427,plain,
% 15.47/2.49      ( k16_lattice3(X0_52,X0_55) = X0_53
% 15.47/2.49      | r3_lattices(X0_52,sK5(X0_52,X0_53,X0_55),X0_53) != iProver_top
% 15.47/2.49      | r3_lattice3(X0_52,X0_53,X0_55) != iProver_top
% 15.47/2.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 15.47/2.49      | v10_lattices(X0_52) != iProver_top
% 15.47/2.49      | v4_lattice3(X0_52) != iProver_top
% 15.47/2.49      | v2_struct_0(X0_52) = iProver_top
% 15.47/2.49      | l3_lattices(X0_52) != iProver_top ),
% 15.47/2.49      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(c_429,plain,
% 15.47/2.49      ( k16_lattice3(sK6,sK8) = sK7
% 15.47/2.49      | r3_lattices(sK6,sK5(sK6,sK7,sK8),sK7) != iProver_top
% 15.47/2.49      | r3_lattice3(sK6,sK7,sK8) != iProver_top
% 15.47/2.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 15.47/2.49      | v10_lattices(sK6) != iProver_top
% 15.47/2.49      | v4_lattice3(sK6) != iProver_top
% 15.47/2.49      | v2_struct_0(sK6) = iProver_top
% 15.47/2.49      | l3_lattices(sK6) != iProver_top ),
% 15.47/2.49      inference(instantiation,[status(thm)],[c_427]) ).
% 15.47/2.49  
% 15.47/2.49  cnf(contradiction,plain,
% 15.47/2.49      ( $false ),
% 15.47/2.49      inference(minisat,
% 15.47/2.49                [status(thm)],
% 15.47/2.49                [c_49580,c_324,c_432,c_429,c_42,c_40,c_39,c_38,c_37,c_36]) ).
% 15.47/2.49  
% 15.47/2.49  
% 15.47/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.47/2.49  
% 15.47/2.49  ------                               Statistics
% 15.47/2.49  
% 15.47/2.49  ------ Selected
% 15.47/2.49  
% 15.47/2.49  total_time:                             1.735
% 15.47/2.49  
%------------------------------------------------------------------------------

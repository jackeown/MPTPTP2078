%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:08 EST 2020

% Result     : Theorem 27.59s
% Output     : CNFRefutation 27.59s
% Verified   : 
% Statistics : Number of formulae       :  388 (11102 expanded)
%              Number of clauses        :  299 (2576 expanded)
%              Number of leaves         :   21 (3216 expanded)
%              Depth                    :   33
%              Number of atoms          : 1821 (116807 expanded)
%              Number of equality atoms :  418 (16281 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2)
                | k16_lattice3(X0,X2) != X1 )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2)
                | k16_lattice3(X0,X2) != X1 )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2)
                | k16_lattice3(X0,X2) != X1 )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK7,X1)
        & r3_lattice3(X0,sK7,X2)
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r3_lattices(X0,X3,X1)
                & r3_lattice3(X0,X3,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r3_lattice3(X0,X1,X2)
            | k16_lattice3(X0,X2) != X1 )
          & ( ( ! [X4] :
                  ( r3_lattices(X0,X4,X1)
                  | ~ r3_lattice3(X0,X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r3_lattice3(X0,X1,X2) )
            | k16_lattice3(X0,X2) = X1 ) )
     => ( ( ? [X3] :
              ( ~ r3_lattices(X0,X3,X1)
              & r3_lattice3(X0,X3,sK6)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r3_lattice3(X0,X1,sK6)
          | k16_lattice3(X0,sK6) != X1 )
        & ( ( ! [X4] :
                ( r3_lattices(X0,X4,X1)
                | ~ r3_lattice3(X0,X4,sK6)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r3_lattice3(X0,X1,sK6) )
          | k16_lattice3(X0,sK6) = X1 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2)
                | k16_lattice3(X0,X2) != X1 )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r3_lattices(X0,X3,sK5)
                  & r3_lattice3(X0,X3,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r3_lattice3(X0,sK5,X2)
              | k16_lattice3(X0,X2) != sK5 )
            & ( ( ! [X4] :
                    ( r3_lattices(X0,X4,sK5)
                    | ~ r3_lattice3(X0,X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r3_lattice3(X0,sK5,X2) )
              | k16_lattice3(X0,X2) = sK5 ) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r3_lattices(X0,X3,X1)
                      & r3_lattice3(X0,X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r3_lattice3(X0,X1,X2)
                  | k16_lattice3(X0,X2) != X1 )
                & ( ( ! [X4] :
                        ( r3_lattices(X0,X4,X1)
                        | ~ r3_lattice3(X0,X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r3_lattice3(X0,X1,X2) )
                  | k16_lattice3(X0,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r3_lattices(sK4,X3,X1)
                    & r3_lattice3(sK4,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(sK4)) )
                | ~ r3_lattice3(sK4,X1,X2)
                | k16_lattice3(sK4,X2) != X1 )
              & ( ( ! [X4] :
                      ( r3_lattices(sK4,X4,X1)
                      | ~ r3_lattice3(sK4,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
                  & r3_lattice3(sK4,X1,X2) )
                | k16_lattice3(sK4,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ( ~ r3_lattices(sK4,sK7,sK5)
        & r3_lattice3(sK4,sK7,sK6)
        & m1_subset_1(sK7,u1_struct_0(sK4)) )
      | ~ r3_lattice3(sK4,sK5,sK6)
      | k16_lattice3(sK4,sK6) != sK5 )
    & ( ( ! [X4] :
            ( r3_lattices(sK4,X4,sK5)
            | ~ r3_lattice3(sK4,X4,sK6)
            | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
        & r3_lattice3(sK4,sK5,sK6) )
      | k16_lattice3(sK4,sK6) = sK5 )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f49,f53,f52,f51,f50])).

fof(f79,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f21,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f81,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X4] :
      ( r3_lattices(sK4,X4,sK5)
      | ~ r3_lattice3(sK4,X4,sK6)
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | k16_lattice3(sK4,sK6) = sK5 ) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f10,plain,(
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

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f58,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f15,plain,(
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
    inference(flattening,[],[f15])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r3_lattice3(sK4,sK5,sK6)
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,
    ( r3_lattice3(sK4,sK7,sK6)
    | ~ r3_lattice3(sK4,sK5,sK6)
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,
    ( ~ r3_lattices(sK4,sK7,sK5)
    | ~ r3_lattice3(sK4,sK5,sK6)
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_813,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_33])).

cnf(c_814,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_30,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_818,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_814,c_30])).

cnf(c_819,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_818])).

cnf(c_2592,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_819])).

cnf(c_90002,plain,
    ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
    | ~ r1_lattices(sK4,sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK0(sK4,X0_53,X0_54))
    | ~ m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_90004,plain,
    ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
    | ~ r1_lattices(sK4,sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK0(sK4,sK5,sK6))
    | ~ m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_90002])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_834,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_33])).

cnf(c_835,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_835,c_30])).

cnf(c_840,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_839])).

cnf(c_2591,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X0_53,X1_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_840])).

cnf(c_5032,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X0_53,sK0(sK4,X1_53,X0_54))
    | ~ r2_hidden(sK0(sK4,X1_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,X1_53,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2591])).

cnf(c_77932,plain,
    ( ~ r3_lattice3(sK4,sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),X0_54)
    | r1_lattices(sK4,sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK0(sK4,X1_53,X0_54))
    | ~ r2_hidden(sK0(sK4,X1_53,X0_54),X0_54)
    | ~ m1_subset_1(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,X1_53,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5032])).

cnf(c_77935,plain,
    ( ~ r3_lattice3(sK4,sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK6)
    | r1_lattices(sK4,sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK0(sK4,sK5,sK6))
    | ~ r2_hidden(sK0(sK4,sK5,sK6),sK6)
    | ~ m1_subset_1(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_77932])).

cnf(c_2615,plain,
    ( ~ r3_lattice3(X0_55,X0_53,X0_54)
    | r3_lattice3(X0_55,X1_53,X0_54)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_13649,plain,
    ( ~ r3_lattice3(sK4,X0_53,sK6)
    | r3_lattice3(sK4,sK1(sK4,X1_53,X0_54),sK6)
    | sK1(sK4,X1_53,X0_54) != X0_53 ),
    inference(instantiation,[status(thm)],[c_2615])).

cnf(c_21131,plain,
    ( ~ r3_lattice3(sK4,sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54),sK6)
    | r3_lattice3(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK6)
    | sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) != sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_13649])).

cnf(c_51149,plain,
    ( ~ r3_lattice3(sK4,sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,sK6)),sK4,sK6),sK6)
    | r3_lattice3(sK4,sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,sK6)),sK6)
    | sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,sK6)) != sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,sK6)),sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_21131])).

cnf(c_51151,plain,
    ( ~ r3_lattice3(sK4,sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6),sK6)
    | r3_lattice3(sK4,sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK6)
    | sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) != sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_51149])).

cnf(c_2611,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_5403,plain,
    ( sK1(sK4,X0_53,X0_54) = sK1(sK4,X0_53,X0_54) ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_11280,plain,
    ( sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) = sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_5403])).

cnf(c_25594,plain,
    ( sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) = sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) ),
    inference(instantiation,[status(thm)],[c_11280])).

cnf(c_25599,plain,
    ( sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) = sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_25594])).

cnf(c_2612,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_4503,plain,
    ( X0_53 != X1_53
    | sK1(sK4,X2_53,X0_54) != X1_53
    | sK1(sK4,X2_53,X0_54) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_5402,plain,
    ( X0_53 != sK1(sK4,X1_53,X0_54)
    | sK1(sK4,X1_53,X0_54) = X0_53
    | sK1(sK4,X1_53,X0_54) != sK1(sK4,X1_53,X0_54) ),
    inference(instantiation,[status(thm)],[c_4503])).

cnf(c_7603,plain,
    ( sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) != sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) = sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54)
    | sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) != sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_5402])).

cnf(c_21158,plain,
    ( sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54) != sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
    | sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) = sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54)
    | sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) != sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) ),
    inference(instantiation,[status(thm)],[c_7603])).

cnf(c_21160,plain,
    ( sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6) != sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
    | sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) = sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6)
    | sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) != sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_21158])).

cnf(c_19,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_733,plain,
    ( ~ l3_lattices(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_33])).

cnf(c_734,plain,
    ( ~ l3_lattices(sK4)
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_738,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_734,c_30])).

cnf(c_2596,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) = k16_lattice3(sK4,X0_54) ),
    inference(subtyping,[status(esa)],[c_738])).

cnf(c_11,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_792,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_33])).

cnf(c_793,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_793,c_30])).

cnf(c_798,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_797])).

cnf(c_2593,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_798])).

cnf(c_3102,plain,
    ( r4_lattice3(sK4,X0_53,X0_54) = iProver_top
    | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2593])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_942,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | sK3(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_943,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ l3_lattices(sK4)
    | sK3(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_947,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | sK3(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_30])).

cnf(c_2586,plain,
    ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
    | sK3(X0_53,sK4,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_947])).

cnf(c_3109,plain,
    ( sK3(X0_53,sK4,X0_54) = X0_53
    | r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2586])).

cnf(c_4024,plain,
    ( sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_3109])).

cnf(c_17,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_31,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_464,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_31])).

cnf(c_465,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_32,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_469,plain,
    ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_33,c_32,c_30])).

cnf(c_470,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_2604,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_470])).

cnf(c_3092,plain,
    ( r4_lattice3(sK4,X0_53,X0_54) != iProver_top
    | r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2604])).

cnf(c_3538,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_3092])).

cnf(c_6,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_903,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_33])).

cnf(c_904,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_908,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_904,c_30])).

cnf(c_909,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_908])).

cnf(c_2588,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_909])).

cnf(c_3107,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
    | r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2588])).

cnf(c_4567,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_3107])).

cnf(c_3515,plain,
    ( ~ r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_3710,plain,
    ( ~ r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54))
    | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3515])).

cnf(c_3712,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54)) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3710])).

cnf(c_3711,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54)
    | ~ r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54))
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2588])).

cnf(c_3716,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3711])).

cnf(c_6601,plain,
    ( m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4567,c_3712,c_3716])).

cnf(c_6602,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6601])).

cnf(c_6607,plain,
    ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_6602])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_861,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_862,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_861])).

cnf(c_866,plain,
    ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_862,c_30])).

cnf(c_867,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_866])).

cnf(c_2590,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_867])).

cnf(c_6818,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54)
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_6819,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6818])).

cnf(c_13666,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6607,c_6819])).

cnf(c_13667,plain,
    ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13666])).

cnf(c_13672,plain,
    ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_13667])).

cnf(c_27,negated_conjecture,
    ( ~ r3_lattice3(sK4,X0,sK6)
    | r3_lattices(sK4,X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_366,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_5])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_370,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_2,c_1])).

cnf(c_607,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_370,c_32])).

cnf(c_608,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_612,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_33,c_30])).

cnf(c_661,plain,
    ( ~ r3_lattice3(sK4,X0,sK6)
    | r1_lattices(sK4,X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | X1 != X0
    | k16_lattice3(sK4,sK6) = sK5
    | sK5 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_612])).

cnf(c_662,plain,
    ( ~ r3_lattice3(sK4,X0,sK6)
    | r1_lattices(sK4,X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,X0,sK5)
    | ~ r3_lattice3(sK4,X0,sK6)
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_29])).

cnf(c_667,plain,
    ( ~ r3_lattice3(sK4,X0,sK6)
    | r1_lattices(sK4,X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(renaming,[status(thm)],[c_666])).

cnf(c_2599,plain,
    ( ~ r3_lattice3(sK4,X0_53,sK6)
    | r1_lattices(sK4,X0_53,sK5)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(subtyping,[status(esa)],[c_667])).

cnf(c_3097,plain,
    ( k16_lattice3(sK4,sK6) = sK5
    | r3_lattice3(sK4,X0_53,sK6) != iProver_top
    | r1_lattices(sK4,X0_53,sK5) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2599])).

cnf(c_14152,plain,
    ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
    | k16_lattice3(sK4,sK6) = sK5
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK5) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13672,c_3097])).

cnf(c_3559,plain,
    ( X0_53 != X1_53
    | X1_53 = X0_53 ),
    inference(resolution,[status(thm)],[c_2612,c_2611])).

cnf(c_4318,plain,
    ( k16_lattice3(sK4,X0_54) = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
    inference(resolution,[status(thm)],[c_3559,c_2596])).

cnf(c_2614,plain,
    ( ~ m1_subset_1(X0_53,X0_56)
    | m1_subset_1(X1_53,X0_56)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_3281,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(X1_53,u1_struct_0(sK4))
    | X1_53 != X0_53 ),
    inference(instantiation,[status(thm)],[c_2614])).

cnf(c_4076,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_54) != X0_53 ),
    inference(instantiation,[status(thm)],[c_3281])).

cnf(c_8725,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_54) != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_4076])).

cnf(c_8726,plain,
    ( k16_lattice3(sK4,X0_54) != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8725])).

cnf(c_18423,plain,
    ( r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK5) = iProver_top
    | k16_lattice3(sK4,sK6) = sK5
    | sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14152,c_4318,c_8726])).

cnf(c_18424,plain,
    ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
    | k16_lattice3(sK4,sK6) = sK5
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK5) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18423])).

cnf(c_18429,plain,
    ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
    | k16_lattice3(sK4,sK6) = sK5
    | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK5) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_18424])).

cnf(c_18567,plain,
    ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
    | k16_lattice3(sK4,sK6) = sK5
    | r1_lattices(sK4,k16_lattice3(sK4,X0_54),sK5) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_18429])).

cnf(c_5649,plain,
    ( k16_lattice3(sK4,X0_54) = k16_lattice3(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_5650,plain,
    ( k16_lattice3(sK4,sK6) = k16_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_5649])).

cnf(c_5795,plain,
    ( k16_lattice3(sK4,X0_54) != X0_53
    | k16_lattice3(sK4,X0_54) = sK5
    | sK5 != X0_53 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_8447,plain,
    ( k16_lattice3(sK4,X0_54) != k16_lattice3(sK4,X0_54)
    | k16_lattice3(sK4,X0_54) = sK5
    | sK5 != k16_lattice3(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_5795])).

cnf(c_8448,plain,
    ( k16_lattice3(sK4,sK6) != k16_lattice3(sK4,sK6)
    | k16_lattice3(sK4,sK6) = sK5
    | sK5 != k16_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_8447])).

cnf(c_4314,plain,
    ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
    | X0_53 = sK3(X0_53,sK4,X0_54) ),
    inference(resolution,[status(thm)],[c_3559,c_2586])).

cnf(c_4899,plain,
    ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
    | X0_53 = X1_53
    | X1_53 != sK3(X0_53,sK4,X0_54) ),
    inference(resolution,[status(thm)],[c_4314,c_2612])).

cnf(c_28,negated_conjecture,
    ( r3_lattice3(sK4,sK5,sK6)
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2607,negated_conjecture,
    ( r3_lattice3(sK4,sK5,sK6)
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3557,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | X0_53 != sK5
    | k16_lattice3(sK4,sK6) = X0_53 ),
    inference(resolution,[status(thm)],[c_2612,c_2607])).

cnf(c_17952,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
    | X0_53 = k16_lattice3(sK4,sK6)
    | sK3(X0_53,sK4,X0_54) != sK5 ),
    inference(resolution,[status(thm)],[c_4899,c_3557])).

cnf(c_18606,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | ~ r2_hidden(sK5,a_2_1_lattice3(sK4,X0_54))
    | sK5 = k16_lattice3(sK4,sK6) ),
    inference(resolution,[status(thm)],[c_17952,c_2586])).

cnf(c_20,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_712,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_713,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_30])).

cnf(c_718,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_717])).

cnf(c_2597,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_718])).

cnf(c_2652,plain,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | r2_hidden(sK5,a_2_1_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2597])).

cnf(c_4320,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | sK5 = k16_lattice3(sK4,sK6) ),
    inference(resolution,[status(thm)],[c_3559,c_2607])).

cnf(c_4334,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | X0_53 != k16_lattice3(sK4,sK6)
    | sK5 = X0_53 ),
    inference(resolution,[status(thm)],[c_4320,c_2612])).

cnf(c_5751,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | k16_lattice3(sK4,sK6) != sK5
    | sK5 = k16_lattice3(sK4,sK6) ),
    inference(resolution,[status(thm)],[c_4334,c_3557])).

cnf(c_2624,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_4079,plain,
    ( k16_lattice3(sK4,X0_54) != X0_53
    | sK5 != X0_53
    | sK5 = k16_lattice3(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_4080,plain,
    ( k16_lattice3(sK4,sK6) != sK5
    | sK5 = k16_lattice3(sK4,sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4079])).

cnf(c_6616,plain,
    ( k16_lattice3(sK4,sK6) != sK5
    | sK5 = k16_lattice3(sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5751,c_2624,c_4080])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_771,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_772,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_776,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_30])).

cnf(c_777,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_776])).

cnf(c_2594,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_777])).

cnf(c_9321,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2594])).

cnf(c_9323,plain,
    ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | m1_subset_1(sK1(sK4,sK5,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9321])).

cnf(c_5800,plain,
    ( r4_lattice3(sK4,sK5,X0_54)
    | ~ r1_lattices(sK4,sK1(sK4,sK5,X0_54),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_9330,plain,
    ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,X0_54))
    | ~ r1_lattices(sK4,sK1(sK4,sK5,a_2_1_lattice3(sK4,X0_54)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5800])).

cnf(c_9334,plain,
    ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | ~ r1_lattices(sK4,sK1(sK4,sK5,a_2_1_lattice3(sK4,sK6)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9330])).

cnf(c_5744,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | sK5 = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
    inference(resolution,[status(thm)],[c_4334,c_2596])).

cnf(c_5770,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | X0_53 != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
    | sK5 = X0_53 ),
    inference(resolution,[status(thm)],[c_5744,c_2612])).

cnf(c_16517,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
    | sK5 = k16_lattice3(sK4,sK6) ),
    inference(resolution,[status(thm)],[c_5770,c_3557])).

cnf(c_4319,plain,
    ( k16_lattice3(sK4,sK6) = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_4318])).

cnf(c_3586,plain,
    ( X0_53 != X1_53
    | X0_53 = k15_lattice3(sK4,X0_54)
    | k15_lattice3(sK4,X0_54) != X1_53 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_4466,plain,
    ( X0_53 != X1_53
    | X0_53 = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) != X1_53 ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_4467,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
    | sK5 = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4466])).

cnf(c_8724,plain,
    ( k16_lattice3(sK4,X0_54) != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
    | sK5 = k16_lattice3(sK4,X0_54)
    | sK5 != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_4079])).

cnf(c_8730,plain,
    ( k16_lattice3(sK4,sK6) != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
    | sK5 = k16_lattice3(sK4,sK6)
    | sK5 != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_8724])).

cnf(c_16859,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
    | sK5 = k16_lattice3(sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16517,c_2624,c_4319,c_4467,c_8730])).

cnf(c_16,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_488,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_489,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_493,plain,
    ( m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_33,c_32,c_30])).

cnf(c_494,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_2603,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0_54,X0_53),u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_15,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_512,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_513,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_33,c_32,c_30])).

cnf(c_518,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_517])).

cnf(c_2602,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r4_lattice3(sK4,sK2(sK4,X0_54,X0_53),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_518])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_744,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_745,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_30])).

cnf(c_750,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_749])).

cnf(c_2595,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X1_53,X0_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_750])).

cnf(c_4681,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X1_53,sK2(sK4,X0_54,X0_53))
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,X0_54,X0_53),u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_54) = X0_53 ),
    inference(resolution,[status(thm)],[c_2602,c_2595])).

cnf(c_4693,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X1_53,sK2(sK4,X0_54,X0_53))
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_54) = X0_53 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2603,c_4681])).

cnf(c_14,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_536,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_537,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_33,c_32,c_30])).

cnf(c_542,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_2601,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | ~ r1_lattices(sK4,X0_53,sK2(sK4,X0_54,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_542])).

cnf(c_13950,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_54) = X0_53 ),
    inference(resolution,[status(thm)],[c_4693,c_2601])).

cnf(c_17024,plain,
    ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,a_2_1_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | sK5 = k16_lattice3(sK4,sK6) ),
    inference(resolution,[status(thm)],[c_16859,c_13950])).

cnf(c_4903,plain,
    ( r3_lattice3(X0_55,X0_53,X0_54)
    | ~ r3_lattice3(X0_55,sK3(X0_53,sK4,X1_54),X0_54)
    | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X1_54)) ),
    inference(resolution,[status(thm)],[c_4314,c_2615])).

cnf(c_21,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_694,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_695,plain,
    ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | r3_lattice3(sK4,sK3(X0,sK4,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_30])).

cnf(c_700,plain,
    ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_2598,plain,
    ( r3_lattice3(sK4,sK3(X0_53,sK4,X0_54),X0_54)
    | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) ),
    inference(subtyping,[status(esa)],[c_700])).

cnf(c_18136,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) ),
    inference(resolution,[status(thm)],[c_4903,c_2598])).

cnf(c_18453,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r3_lattice3(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_18136,c_2593])).

cnf(c_18588,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,sK6))
    | r1_lattices(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,sK6)),sK5)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,X0_53,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(resolution,[status(thm)],[c_18453,c_2599])).

cnf(c_18590,plain,
    ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | r1_lattices(sK4,sK1(sK4,sK5,a_2_1_lattice3(sK4,sK6)),sK5)
    | ~ m1_subset_1(sK1(sK4,sK5,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_18588])).

cnf(c_18611,plain,
    ( sK5 = k16_lattice3(sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18606,c_29,c_2652,c_4320,c_6616,c_9323,c_9334,c_17024,c_18590])).

cnf(c_18742,plain,
    ( k16_lattice3(sK4,sK6) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18567,c_29,c_2652,c_4320,c_5650,c_6616,c_8448,c_9323,c_9334,c_17024,c_18590])).

cnf(c_26,negated_conjecture,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | m1_subset_1(sK7,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2608,negated_conjecture,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | m1_subset_1(sK7,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3088,plain,
    ( k16_lattice3(sK4,sK6) != sK5
    | r3_lattice3(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2608])).

cnf(c_18745,plain,
    ( r3_lattice3(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18742,c_3088])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | r3_lattice3(sK4,sK7,sK6)
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2609,negated_conjecture,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | r3_lattice3(sK4,sK7,sK6)
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2625,plain,
    ( k16_lattice3(sK4,sK6) != sK5
    | r3_lattice3(sK4,sK5,sK6) != iProver_top
    | r3_lattice3(sK4,sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2609])).

cnf(c_2626,plain,
    ( k16_lattice3(sK4,sK6) != sK5
    | r3_lattice3(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2608])).

cnf(c_24,negated_conjecture,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | ~ r3_lattices(sK4,sK7,sK5)
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f88])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_398,plain,
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

cnf(c_402,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_2,c_1])).

cnf(c_583,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_402,c_32])).

cnf(c_584,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_588,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_33,c_30])).

cnf(c_644,plain,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | ~ r1_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) != sK5
    | sK5 != X1
    | sK7 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_588])).

cnf(c_645,plain,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | ~ r1_lattices(sK4,sK7,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_647,plain,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | ~ r1_lattices(sK4,sK7,sK5)
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_29,c_26])).

cnf(c_2600,plain,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | ~ r1_lattices(sK4,sK7,sK5)
    | k16_lattice3(sK4,sK6) != sK5 ),
    inference(subtyping,[status(esa)],[c_647])).

cnf(c_2644,plain,
    ( k16_lattice3(sK4,sK6) != sK5
    | r3_lattice3(sK4,sK5,sK6) != iProver_top
    | r1_lattices(sK4,sK7,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2600])).

cnf(c_2654,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = k16_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2596])).

cnf(c_3555,plain,
    ( X0_53 != k16_lattice3(sK4,X0_54)
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) = X0_53 ),
    inference(resolution,[status(thm)],[c_2612,c_2596])).

cnf(c_3556,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = sK5
    | sK5 != k16_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_3555])).

cnf(c_18,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_446,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_447,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_451,plain,
    ( ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_33,c_32,c_30])).

cnf(c_452,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_2605,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54)
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_3848,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54))
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2605])).

cnf(c_3853,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3848])).

cnf(c_3855,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3853])).

cnf(c_3490,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_54) != X0_53 ),
    inference(instantiation,[status(thm)],[c_3281])).

cnf(c_4192,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) != X0_53 ),
    inference(instantiation,[status(thm)],[c_3490])).

cnf(c_4193,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) != X0_53
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4192])).

cnf(c_4195,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4193])).

cnf(c_4461,plain,
    ( X0_53 != k16_lattice3(sK4,X0_54)
    | X0_53 = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) != k16_lattice3(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_4462,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != k16_lattice3(sK4,sK6)
    | sK5 != k16_lattice3(sK4,sK6)
    | sK5 = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_4461])).

cnf(c_2617,plain,
    ( ~ r4_lattice3(X0_55,X0_53,X0_54)
    | r4_lattice3(X0_55,X1_53,X0_54)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_3410,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54)
    | X0_53 != k15_lattice3(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_2617])).

cnf(c_5072,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | ~ r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54))
    | X0_53 != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_3410])).

cnf(c_5073,plain,
    ( X0_53 != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
    | r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) = iProver_top
    | r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5072])).

cnf(c_5075,plain,
    ( sK5 != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
    | r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) != iProver_top
    | r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5073])).

cnf(c_4948,plain,
    ( ~ r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r1_lattices(sK4,X1_53,X0_53)
    | ~ r2_hidden(X1_53,a_2_1_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2595])).

cnf(c_5817,plain,
    ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,X0_54))
    | r1_lattices(sK4,sK7,sK5)
    | ~ r2_hidden(sK7,a_2_1_lattice3(sK4,X0_54))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4948])).

cnf(c_5818,plain,
    ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | r1_lattices(sK4,sK7,sK5) = iProver_top
    | r2_hidden(sK7,a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5817])).

cnf(c_5820,plain,
    ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6)) != iProver_top
    | r1_lattices(sK4,sK7,sK5) = iProver_top
    | r2_hidden(sK7,a_2_1_lattice3(sK4,sK6)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5818])).

cnf(c_13572,plain,
    ( ~ r3_lattice3(sK4,sK7,X0_54)
    | r2_hidden(sK7,a_2_1_lattice3(sK4,X0_54))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2597])).

cnf(c_13573,plain,
    ( r3_lattice3(sK4,sK7,X0_54) != iProver_top
    | r2_hidden(sK7,a_2_1_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13572])).

cnf(c_13575,plain,
    ( r3_lattice3(sK4,sK7,sK6) != iProver_top
    | r2_hidden(sK7,a_2_1_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13573])).

cnf(c_18785,plain,
    ( r3_lattice3(sK4,sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18745,c_29,c_38,c_2625,c_2626,c_2644,c_2652,c_2654,c_3556,c_3855,c_4195,c_4320,c_4462,c_5075,c_5650,c_5820,c_6616,c_8448,c_9323,c_9334,c_13575,c_17024,c_18590])).

cnf(c_18787,plain,
    ( ~ r3_lattice3(sK4,sK5,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18785])).

cnf(c_3105,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2590])).

cnf(c_6608,plain,
    ( r4_lattice3(sK4,sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_6602])).

cnf(c_6701,plain,
    ( r4_lattice3(sK4,sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3105,c_6608])).

cnf(c_18750,plain,
    ( r4_lattice3(sK4,sK0(sK4,sK5,X0_54),a_2_1_lattice3(sK4,sK6)) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),X0_54) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18742,c_6701])).

cnf(c_18768,plain,
    ( ~ r4_lattice3(sK4,sK0(sK4,sK5,X0_54),a_2_1_lattice3(sK4,sK6))
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),X0_54)
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18750])).

cnf(c_18770,plain,
    ( ~ r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK6)
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_18768])).

cnf(c_18769,plain,
    ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK6) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18750])).

cnf(c_3376,plain,
    ( ~ r2_hidden(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54))
    | sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_2586])).

cnf(c_13381,plain,
    ( ~ r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54))
    | sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54) = sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) ),
    inference(instantiation,[status(thm)],[c_3376])).

cnf(c_13382,plain,
    ( sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54) = sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
    | r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13381])).

cnf(c_13384,plain,
    ( sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6) = sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
    | r2_hidden(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13382])).

cnf(c_5920,plain,
    ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),X1_54)
    | m1_subset_1(sK1(sK4,sK0(sK4,X0_53,X0_54),X1_54),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2594])).

cnf(c_8034,plain,
    ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
    | m1_subset_1(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5920])).

cnf(c_8037,plain,
    ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
    | m1_subset_1(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8034])).

cnf(c_3375,plain,
    ( r3_lattice3(sK4,sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54),X0_54)
    | ~ r2_hidden(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_2598])).

cnf(c_6950,plain,
    ( r3_lattice3(sK4,sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54),X1_54)
    | ~ r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54)) ),
    inference(instantiation,[status(thm)],[c_3375])).

cnf(c_6952,plain,
    ( r3_lattice3(sK4,sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6),sK6)
    | ~ r2_hidden(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_6950])).

cnf(c_5778,plain,
    ( ~ r3_lattice3(X0_55,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),X0_54)
    | r3_lattice3(X0_55,sK5,X0_54)
    | r3_lattice3(sK4,sK5,sK6) ),
    inference(resolution,[status(thm)],[c_5744,c_2615])).

cnf(c_5783,plain,
    ( r3_lattice3(X0_55,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),X0_54) != iProver_top
    | r3_lattice3(X0_55,sK5,X0_54) = iProver_top
    | r3_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5778])).

cnf(c_5785,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK6) != iProver_top
    | r3_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5783])).

cnf(c_5784,plain,
    ( ~ r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK6)
    | r3_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_5778])).

cnf(c_4194,plain,
    ( m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5 ),
    inference(instantiation,[status(thm)],[c_4192])).

cnf(c_3374,plain,
    ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
    | r2_hidden(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_3619,plain,
    ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
    | r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54))
    | ~ m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3374])).

cnf(c_3624,plain,
    ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) = iProver_top
    | r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54)) = iProver_top
    | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3619])).

cnf(c_3626,plain,
    ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) = iProver_top
    | r2_hidden(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3624])).

cnf(c_3625,plain,
    ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
    | r2_hidden(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3619])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_882,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_883,plain,
    ( r3_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_882])).

cnf(c_887,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_883,c_30])).

cnf(c_888,plain,
    ( r3_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_887])).

cnf(c_2589,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_888])).

cnf(c_2674,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | r2_hidden(sK0(sK4,sK5,sK6),sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_2670,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2590])).

cnf(c_2672,plain,
    ( r3_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2670])).

cnf(c_2671,plain,
    ( r3_lattice3(sK4,sK5,sK6)
    | m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_90004,c_77935,c_51151,c_25599,c_21160,c_18787,c_18785,c_18770,c_18769,c_18611,c_13384,c_8037,c_6952,c_5785,c_5784,c_4195,c_4194,c_3626,c_3625,c_3556,c_2674,c_2672,c_2671,c_38,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:40:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.59/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.59/3.99  
% 27.59/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.59/3.99  
% 27.59/3.99  ------  iProver source info
% 27.59/3.99  
% 27.59/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.59/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.59/3.99  git: non_committed_changes: false
% 27.59/3.99  git: last_make_outside_of_git: false
% 27.59/3.99  
% 27.59/3.99  ------ 
% 27.59/3.99  ------ Parsing...
% 27.59/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.59/3.99  
% 27.59/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 27.59/3.99  
% 27.59/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.59/3.99  
% 27.59/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.59/3.99  ------ Proving...
% 27.59/3.99  ------ Problem Properties 
% 27.59/3.99  
% 27.59/3.99  
% 27.59/3.99  clauses                                 24
% 27.59/3.99  conjectures                             4
% 27.59/3.99  EPR                                     0
% 27.59/3.99  Horn                                    16
% 27.59/3.99  unary                                   2
% 27.59/3.99  binary                                  5
% 27.59/3.99  lits                                    72
% 27.59/3.99  lits eq                                 10
% 27.59/3.99  fd_pure                                 0
% 27.59/3.99  fd_pseudo                               0
% 27.59/3.99  fd_cond                                 0
% 27.59/3.99  fd_pseudo_cond                          3
% 27.59/3.99  AC symbols                              0
% 27.59/3.99  
% 27.59/3.99  ------ Input Options Time Limit: Unbounded
% 27.59/3.99  
% 27.59/3.99  
% 27.59/3.99  ------ 
% 27.59/3.99  Current options:
% 27.59/3.99  ------ 
% 27.59/3.99  
% 27.59/3.99  
% 27.59/3.99  
% 27.59/3.99  
% 27.59/3.99  ------ Proving...
% 27.59/3.99  
% 27.59/3.99  
% 27.59/3.99  % SZS status Theorem for theBenchmark.p
% 27.59/3.99  
% 27.59/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.59/3.99  
% 27.59/3.99  fof(f4,axiom,(
% 27.59/3.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 27.59/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.59/3.99  
% 27.59/3.99  fof(f19,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 27.59/3.99    inference(ennf_transformation,[],[f4])).
% 27.59/3.99  
% 27.59/3.99  fof(f20,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(flattening,[],[f19])).
% 27.59/3.99  
% 27.59/3.99  fof(f34,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(nnf_transformation,[],[f20])).
% 27.59/3.99  
% 27.59/3.99  fof(f35,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(rectify,[],[f34])).
% 27.59/3.99  
% 27.59/3.99  fof(f36,plain,(
% 27.59/3.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 27.59/3.99    introduced(choice_axiom,[])).
% 27.59/3.99  
% 27.59/3.99  fof(f37,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 27.59/3.99  
% 27.59/3.99  fof(f68,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f37])).
% 27.59/3.99  
% 27.59/3.99  fof(f8,conjecture,(
% 27.59/3.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 27.59/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.59/3.99  
% 27.59/3.99  fof(f9,negated_conjecture,(
% 27.59/3.99    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 27.59/3.99    inference(negated_conjecture,[],[f8])).
% 27.59/3.99  
% 27.59/3.99  fof(f27,plain,(
% 27.59/3.99    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) = X1 <~> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 27.59/3.99    inference(ennf_transformation,[],[f9])).
% 27.59/3.99  
% 27.59/3.99  fof(f28,plain,(
% 27.59/3.99    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) = X1 <~> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 27.59/3.99    inference(flattening,[],[f27])).
% 27.59/3.99  
% 27.59/3.99  fof(f47,plain,(
% 27.59/3.99    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 27.59/3.99    inference(nnf_transformation,[],[f28])).
% 27.59/3.99  
% 27.59/3.99  fof(f48,plain,(
% 27.59/3.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 27.59/3.99    inference(flattening,[],[f47])).
% 27.59/3.99  
% 27.59/3.99  fof(f49,plain,(
% 27.59/3.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 27.59/3.99    inference(rectify,[],[f48])).
% 27.59/3.99  
% 27.59/3.99  fof(f53,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK7,X1) & r3_lattice3(X0,sK7,X2) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 27.59/3.99    introduced(choice_axiom,[])).
% 27.59/3.99  
% 27.59/3.99  fof(f52,plain,(
% 27.59/3.99    ( ! [X0,X1] : (? [X2] : ((? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) => ((? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,sK6) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,sK6) | k16_lattice3(X0,sK6) != X1) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,sK6) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,sK6)) | k16_lattice3(X0,sK6) = X1))) )),
% 27.59/3.99    introduced(choice_axiom,[])).
% 27.59/3.99  
% 27.59/3.99  fof(f51,plain,(
% 27.59/3.99    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((? [X3] : (~r3_lattices(X0,X3,sK5) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,sK5,X2) | k16_lattice3(X0,X2) != sK5) & ((! [X4] : (r3_lattices(X0,X4,sK5) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,sK5,X2)) | k16_lattice3(X0,X2) = sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 27.59/3.99    introduced(choice_axiom,[])).
% 27.59/3.99  
% 27.59/3.99  fof(f50,plain,(
% 27.59/3.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (~r3_lattices(sK4,X3,X1) & r3_lattice3(sK4,X3,X2) & m1_subset_1(X3,u1_struct_0(sK4))) | ~r3_lattice3(sK4,X1,X2) | k16_lattice3(sK4,X2) != X1) & ((! [X4] : (r3_lattices(sK4,X4,X1) | ~r3_lattice3(sK4,X4,X2) | ~m1_subset_1(X4,u1_struct_0(sK4))) & r3_lattice3(sK4,X1,X2)) | k16_lattice3(sK4,X2) = X1)) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 27.59/3.99    introduced(choice_axiom,[])).
% 27.59/3.99  
% 27.59/3.99  fof(f54,plain,(
% 27.59/3.99    ((((~r3_lattices(sK4,sK7,sK5) & r3_lattice3(sK4,sK7,sK6) & m1_subset_1(sK7,u1_struct_0(sK4))) | ~r3_lattice3(sK4,sK5,sK6) | k16_lattice3(sK4,sK6) != sK5) & ((! [X4] : (r3_lattices(sK4,X4,sK5) | ~r3_lattice3(sK4,X4,sK6) | ~m1_subset_1(X4,u1_struct_0(sK4))) & r3_lattice3(sK4,sK5,sK6)) | k16_lattice3(sK4,sK6) = sK5)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 27.59/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f49,f53,f52,f51,f50])).
% 27.59/3.99  
% 27.59/3.99  fof(f79,plain,(
% 27.59/3.99    ~v2_struct_0(sK4)),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f82,plain,(
% 27.59/3.99    l3_lattices(sK4)),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f3,axiom,(
% 27.59/3.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 27.59/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.59/3.99  
% 27.59/3.99  fof(f17,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 27.59/3.99    inference(ennf_transformation,[],[f3])).
% 27.59/3.99  
% 27.59/3.99  fof(f18,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(flattening,[],[f17])).
% 27.59/3.99  
% 27.59/3.99  fof(f30,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(nnf_transformation,[],[f18])).
% 27.59/3.99  
% 27.59/3.99  fof(f31,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(rectify,[],[f30])).
% 27.59/3.99  
% 27.59/3.99  fof(f32,plain,(
% 27.59/3.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 27.59/3.99    introduced(choice_axiom,[])).
% 27.59/3.99  
% 27.59/3.99  fof(f33,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 27.59/3.99  
% 27.59/3.99  fof(f61,plain,(
% 27.59/3.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f33])).
% 27.59/3.99  
% 27.59/3.99  fof(f6,axiom,(
% 27.59/3.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1))),
% 27.59/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.59/3.99  
% 27.59/3.99  fof(f23,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 27.59/3.99    inference(ennf_transformation,[],[f6])).
% 27.59/3.99  
% 27.59/3.99  fof(f24,plain,(
% 27.59/3.99    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(flattening,[],[f23])).
% 27.59/3.99  
% 27.59/3.99  fof(f74,plain,(
% 27.59/3.99    ( ! [X0,X1] : (k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f24])).
% 27.59/3.99  
% 27.59/3.99  fof(f67,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f37])).
% 27.59/3.99  
% 27.59/3.99  fof(f7,axiom,(
% 27.59/3.99    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 27.59/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.59/3.99  
% 27.59/3.99  fof(f25,plain,(
% 27.59/3.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 27.59/3.99    inference(ennf_transformation,[],[f7])).
% 27.59/3.99  
% 27.59/3.99  fof(f26,plain,(
% 27.59/3.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 27.59/3.99    inference(flattening,[],[f25])).
% 27.59/3.99  
% 27.59/3.99  fof(f43,plain,(
% 27.59/3.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 27.59/3.99    inference(nnf_transformation,[],[f26])).
% 27.59/3.99  
% 27.59/3.99  fof(f44,plain,(
% 27.59/3.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 27.59/3.99    inference(rectify,[],[f43])).
% 27.59/3.99  
% 27.59/3.99  fof(f45,plain,(
% 27.59/3.99    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 27.59/3.99    introduced(choice_axiom,[])).
% 27.59/3.99  
% 27.59/3.99  fof(f46,plain,(
% 27.59/3.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 27.59/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 27.59/3.99  
% 27.59/3.99  fof(f76,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f46])).
% 27.59/3.99  
% 27.59/3.99  fof(f5,axiom,(
% 27.59/3.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 27.59/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.59/3.99  
% 27.59/3.99  fof(f21,plain,(
% 27.59/3.99    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 27.59/3.99    inference(ennf_transformation,[],[f5])).
% 27.59/3.99  
% 27.59/3.99  fof(f22,plain,(
% 27.59/3.99    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(flattening,[],[f21])).
% 27.59/3.99  
% 27.59/3.99  fof(f38,plain,(
% 27.59/3.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(nnf_transformation,[],[f22])).
% 27.59/3.99  
% 27.59/3.99  fof(f39,plain,(
% 27.59/3.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(flattening,[],[f38])).
% 27.59/3.99  
% 27.59/3.99  fof(f40,plain,(
% 27.59/3.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(rectify,[],[f39])).
% 27.59/3.99  
% 27.59/3.99  fof(f41,plain,(
% 27.59/3.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 27.59/3.99    introduced(choice_axiom,[])).
% 27.59/3.99  
% 27.59/3.99  fof(f42,plain,(
% 27.59/3.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 27.59/3.99  
% 27.59/3.99  fof(f70,plain,(
% 27.59/3.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f42])).
% 27.59/3.99  
% 27.59/3.99  fof(f89,plain,(
% 27.59/3.99    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(equality_resolution,[],[f70])).
% 27.59/3.99  
% 27.59/3.99  fof(f81,plain,(
% 27.59/3.99    v4_lattice3(sK4)),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f80,plain,(
% 27.59/3.99    v10_lattices(sK4)),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f64,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f33])).
% 27.59/3.99  
% 27.59/3.99  fof(f62,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f33])).
% 27.59/3.99  
% 27.59/3.99  fof(f85,plain,(
% 27.59/3.99    ( ! [X4] : (r3_lattices(sK4,X4,sK5) | ~r3_lattice3(sK4,X4,sK6) | ~m1_subset_1(X4,u1_struct_0(sK4)) | k16_lattice3(sK4,sK6) = sK5) )),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f1,axiom,(
% 27.59/3.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 27.59/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.59/3.99  
% 27.59/3.99  fof(f10,plain,(
% 27.59/3.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 27.59/3.99    inference(pure_predicate_removal,[],[f1])).
% 27.59/3.99  
% 27.59/3.99  fof(f11,plain,(
% 27.59/3.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 27.59/3.99    inference(pure_predicate_removal,[],[f10])).
% 27.59/3.99  
% 27.59/3.99  fof(f12,plain,(
% 27.59/3.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 27.59/3.99    inference(pure_predicate_removal,[],[f11])).
% 27.59/3.99  
% 27.59/3.99  fof(f13,plain,(
% 27.59/3.99    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 27.59/3.99    inference(ennf_transformation,[],[f12])).
% 27.59/3.99  
% 27.59/3.99  fof(f14,plain,(
% 27.59/3.99    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 27.59/3.99    inference(flattening,[],[f13])).
% 27.59/3.99  
% 27.59/3.99  fof(f58,plain,(
% 27.59/3.99    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f14])).
% 27.59/3.99  
% 27.59/3.99  fof(f2,axiom,(
% 27.59/3.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 27.59/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.59/3.99  
% 27.59/3.99  fof(f15,plain,(
% 27.59/3.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 27.59/3.99    inference(ennf_transformation,[],[f2])).
% 27.59/3.99  
% 27.59/3.99  fof(f16,plain,(
% 27.59/3.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(flattening,[],[f15])).
% 27.59/3.99  
% 27.59/3.99  fof(f29,plain,(
% 27.59/3.99    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 27.59/3.99    inference(nnf_transformation,[],[f16])).
% 27.59/3.99  
% 27.59/3.99  fof(f59,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f29])).
% 27.59/3.99  
% 27.59/3.99  fof(f56,plain,(
% 27.59/3.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f14])).
% 27.59/3.99  
% 27.59/3.99  fof(f57,plain,(
% 27.59/3.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f14])).
% 27.59/3.99  
% 27.59/3.99  fof(f83,plain,(
% 27.59/3.99    m1_subset_1(sK5,u1_struct_0(sK4))),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f84,plain,(
% 27.59/3.99    r3_lattice3(sK4,sK5,sK6) | k16_lattice3(sK4,sK6) = sK5),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f78,plain,(
% 27.59/3.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f46])).
% 27.59/3.99  
% 27.59/3.99  fof(f91,plain,(
% 27.59/3.99    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 27.59/3.99    inference(equality_resolution,[],[f78])).
% 27.59/3.99  
% 27.59/3.99  fof(f66,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f37])).
% 27.59/3.99  
% 27.59/3.99  fof(f71,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f42])).
% 27.59/3.99  
% 27.59/3.99  fof(f72,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK2(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f42])).
% 27.59/3.99  
% 27.59/3.99  fof(f65,plain,(
% 27.59/3.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f37])).
% 27.59/3.99  
% 27.59/3.99  fof(f73,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK2(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f42])).
% 27.59/3.99  
% 27.59/3.99  fof(f77,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK3(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f46])).
% 27.59/3.99  
% 27.59/3.99  fof(f86,plain,(
% 27.59/3.99    m1_subset_1(sK7,u1_struct_0(sK4)) | ~r3_lattice3(sK4,sK5,sK6) | k16_lattice3(sK4,sK6) != sK5),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f87,plain,(
% 27.59/3.99    r3_lattice3(sK4,sK7,sK6) | ~r3_lattice3(sK4,sK5,sK6) | k16_lattice3(sK4,sK6) != sK5),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f88,plain,(
% 27.59/3.99    ~r3_lattices(sK4,sK7,sK5) | ~r3_lattice3(sK4,sK5,sK6) | k16_lattice3(sK4,sK6) != sK5),
% 27.59/3.99    inference(cnf_transformation,[],[f54])).
% 27.59/3.99  
% 27.59/3.99  fof(f60,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f29])).
% 27.59/3.99  
% 27.59/3.99  fof(f69,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f42])).
% 27.59/3.99  
% 27.59/3.99  fof(f90,plain,(
% 27.59/3.99    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(equality_resolution,[],[f69])).
% 27.59/3.99  
% 27.59/3.99  fof(f63,plain,(
% 27.59/3.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.59/3.99    inference(cnf_transformation,[],[f33])).
% 27.59/3.99  
% 27.59/3.99  cnf(c_10,plain,
% 27.59/3.99      ( r4_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f68]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_33,negated_conjecture,
% 27.59/3.99      ( ~ v2_struct_0(sK4) ),
% 27.59/3.99      inference(cnf_transformation,[],[f79]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_813,plain,
% 27.59/3.99      ( r4_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_10,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_814,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_813]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_30,negated_conjecture,
% 27.59/3.99      ( l3_lattices(sK4) ),
% 27.59/3.99      inference(cnf_transformation,[],[f82]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_818,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 27.59/3.99      | r4_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_814,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_819,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_818]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2592,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_819]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_90002,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK0(sK4,X0_53,X0_54))
% 27.59/3.99      | ~ m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2592]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_90004,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK0(sK4,sK5,sK6))
% 27.59/3.99      | ~ m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_90002]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_9,plain,
% 27.59/3.99      ( ~ r3_lattice3(X0,X1,X2)
% 27.59/3.99      | r1_lattices(X0,X1,X3)
% 27.59/3.99      | ~ r2_hidden(X3,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_834,plain,
% 27.59/3.99      ( ~ r3_lattice3(X0,X1,X2)
% 27.59/3.99      | r1_lattices(X0,X1,X3)
% 27.59/3.99      | ~ r2_hidden(X3,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_9,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_835,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0,X1)
% 27.59/3.99      | r1_lattices(sK4,X0,X2)
% 27.59/3.99      | ~ r2_hidden(X2,X1)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_834]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_839,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 27.59/3.99      | ~ r2_hidden(X2,X1)
% 27.59/3.99      | r1_lattices(sK4,X0,X2)
% 27.59/3.99      | ~ r3_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_835,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_840,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0,X1)
% 27.59/3.99      | r1_lattices(sK4,X0,X2)
% 27.59/3.99      | ~ r2_hidden(X2,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_839]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2591,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r1_lattices(sK4,X0_53,X1_53)
% 27.59/3.99      | ~ r2_hidden(X1_53,X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_840]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5032,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r1_lattices(sK4,X0_53,sK0(sK4,X1_53,X0_54))
% 27.59/3.99      | ~ r2_hidden(sK0(sK4,X1_53,X0_54),X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK0(sK4,X1_53,X0_54),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2591]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_77932,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),X0_54)
% 27.59/3.99      | r1_lattices(sK4,sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK0(sK4,X1_53,X0_54))
% 27.59/3.99      | ~ r2_hidden(sK0(sK4,X1_53,X0_54),X0_54)
% 27.59/3.99      | ~ m1_subset_1(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK0(sK4,X1_53,X0_54),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_5032]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_77935,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK6)
% 27.59/3.99      | r1_lattices(sK4,sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK0(sK4,sK5,sK6))
% 27.59/3.99      | ~ r2_hidden(sK0(sK4,sK5,sK6),sK6)
% 27.59/3.99      | ~ m1_subset_1(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_77932]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2615,plain,
% 27.59/3.99      ( ~ r3_lattice3(X0_55,X0_53,X0_54)
% 27.59/3.99      | r3_lattice3(X0_55,X1_53,X0_54)
% 27.59/3.99      | X1_53 != X0_53 ),
% 27.59/3.99      theory(equality) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13649,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0_53,sK6)
% 27.59/3.99      | r3_lattice3(sK4,sK1(sK4,X1_53,X0_54),sK6)
% 27.59/3.99      | sK1(sK4,X1_53,X0_54) != X0_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2615]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_21131,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54),sK6)
% 27.59/3.99      | r3_lattice3(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK6)
% 27.59/3.99      | sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) != sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_13649]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_51149,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,sK6)),sK4,sK6),sK6)
% 27.59/3.99      | r3_lattice3(sK4,sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,sK6)),sK6)
% 27.59/3.99      | sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,sK6)) != sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,sK6)),sK4,sK6) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_21131]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_51151,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6),sK6)
% 27.59/3.99      | r3_lattice3(sK4,sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK6)
% 27.59/3.99      | sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) != sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_51149]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2611,plain,( X0_53 = X0_53 ),theory(equality) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5403,plain,
% 27.59/3.99      ( sK1(sK4,X0_53,X0_54) = sK1(sK4,X0_53,X0_54) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2611]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_11280,plain,
% 27.59/3.99      ( sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) = sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_5403]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_25594,plain,
% 27.59/3.99      ( sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) = sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_11280]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_25599,plain,
% 27.59/3.99      ( sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) = sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_25594]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2612,plain,
% 27.59/3.99      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 27.59/3.99      theory(equality) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4503,plain,
% 27.59/3.99      ( X0_53 != X1_53
% 27.59/3.99      | sK1(sK4,X2_53,X0_54) != X1_53
% 27.59/3.99      | sK1(sK4,X2_53,X0_54) = X0_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2612]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5402,plain,
% 27.59/3.99      ( X0_53 != sK1(sK4,X1_53,X0_54)
% 27.59/3.99      | sK1(sK4,X1_53,X0_54) = X0_53
% 27.59/3.99      | sK1(sK4,X1_53,X0_54) != sK1(sK4,X1_53,X0_54) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4503]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_7603,plain,
% 27.59/3.99      ( sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) != sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) = sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54)
% 27.59/3.99      | sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) != sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_5402]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_21158,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54) != sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
% 27.59/3.99      | sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) = sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54)
% 27.59/3.99      | sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) != sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_7603]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_21160,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6) != sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) = sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6)
% 27.59/3.99      | sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) != sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_21158]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_19,plain,
% 27.59/3.99      ( ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
% 27.59/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_733,plain,
% 27.59/3.99      ( ~ l3_lattices(X0)
% 27.59/3.99      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_19,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_734,plain,
% 27.59/3.99      ( ~ l3_lattices(sK4)
% 27.59/3.99      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_733]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_738,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_734,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2596,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) = k16_lattice3(sK4,X0_54) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_738]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_11,plain,
% 27.59/3.99      ( r4_lattice3(X0,X1,X2)
% 27.59/3.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f67]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_792,plain,
% 27.59/3.99      ( r4_lattice3(X0,X1,X2)
% 27.59/3.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_11,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_793,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | r2_hidden(sK1(sK4,X0,X1),X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_792]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_797,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | r2_hidden(sK1(sK4,X0,X1),X1)
% 27.59/3.99      | r4_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_793,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_798,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | r2_hidden(sK1(sK4,X0,X1),X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_797]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2593,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_798]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3102,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,X0_54) = iProver_top
% 27.59/3.99      | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54) = iProver_top
% 27.59/3.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2593]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_22,plain,
% 27.59/3.99      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 27.59/3.99      | ~ l3_lattices(X1)
% 27.59/3.99      | v2_struct_0(X1)
% 27.59/3.99      | sK3(X0,X1,X2) = X0 ),
% 27.59/3.99      inference(cnf_transformation,[],[f76]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_942,plain,
% 27.59/3.99      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 27.59/3.99      | ~ l3_lattices(X1)
% 27.59/3.99      | sK3(X0,X1,X2) = X0
% 27.59/3.99      | sK4 != X1 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_943,plain,
% 27.59/3.99      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 27.59/3.99      | ~ l3_lattices(sK4)
% 27.59/3.99      | sK3(X0,sK4,X1) = X0 ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_942]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_947,plain,
% 27.59/3.99      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) | sK3(X0,sK4,X1) = X0 ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_943,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2586,plain,
% 27.59/3.99      ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | sK3(X0_53,sK4,X0_54) = X0_53 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_947]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3109,plain,
% 27.59/3.99      ( sK3(X0_53,sK4,X0_54) = X0_53
% 27.59/3.99      | r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2586]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4024,plain,
% 27.59/3.99      ( sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) = iProver_top
% 27.59/3.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_3102,c_3109]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_17,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 27.59/3.99      | ~ v4_lattice3(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f89]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_31,negated_conjecture,
% 27.59/3.99      ( v4_lattice3(sK4) ),
% 27.59/3.99      inference(cnf_transformation,[],[f81]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_464,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_17,c_31]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_465,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4)
% 27.59/3.99      | v2_struct_0(sK4)
% 27.59/3.99      | ~ v10_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_464]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_32,negated_conjecture,
% 27.59/3.99      ( v10_lattices(sK4) ),
% 27.59/3.99      inference(cnf_transformation,[],[f80]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_469,plain,
% 27.59/3.99      ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 27.59/3.99      | ~ r4_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_465,c_33,c_32,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_470,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_469]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2604,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_470]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3092,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,X0_54) != iProver_top
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53) = iProver_top
% 27.59/3.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2604]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3538,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X0_53) = iProver_top
% 27.59/3.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_2596,c_3092]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6,plain,
% 27.59/3.99      ( r3_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f64]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_903,plain,
% 27.59/3.99      ( r3_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_6,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_904,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_903]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_908,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 27.59/3.99      | r3_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_904,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_909,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_908]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2588,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54))
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_909]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3107,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
% 27.59/3.99      | r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54)) != iProver_top
% 27.59/3.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2588]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4567,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_3538,c_3107]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3515,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X0_53)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2604]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3710,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54))
% 27.59/3.99      | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3515]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3712,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54)) = iProver_top
% 27.59/3.99      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_3710]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3711,plain,
% 27.59/3.99      ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54)
% 27.59/3.99      | ~ r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2588]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3716,plain,
% 27.59/3.99      ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_3711]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6601,plain,
% 27.59/3.99      ( m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_4567,c_3712,c_3716]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6602,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_6601]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6607,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_4024,c_6602]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_8,plain,
% 27.59/3.99      ( r3_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_861,plain,
% 27.59/3.99      ( r3_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_862,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_861]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_866,plain,
% 27.59/3.99      ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | r3_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_862,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_867,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_866]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2590,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_867]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6818,plain,
% 27.59/3.99      ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54)
% 27.59/3.99      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2590]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6819,plain,
% 27.59/3.99      ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_6818]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13666,plain,
% 27.59/3.99      ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_6607,c_6819]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13667,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_13666]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13672,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_2596,c_13667]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_27,negated_conjecture,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0,sK6)
% 27.59/3.99      | r3_lattices(sK4,X0,sK5)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(cnf_transformation,[],[f85]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_0,plain,
% 27.59/3.99      ( ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | v9_lattices(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f58]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5,plain,
% 27.59/3.99      ( r1_lattices(X0,X1,X2)
% 27.59/3.99      | ~ r3_lattices(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ v6_lattices(X0)
% 27.59/3.99      | ~ v8_lattices(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v9_lattices(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f59]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_366,plain,
% 27.59/3.99      ( r1_lattices(X0,X1,X2)
% 27.59/3.99      | ~ r3_lattices(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ v6_lattices(X0)
% 27.59/3.99      | ~ v8_lattices(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_0,c_5]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2,plain,
% 27.59/3.99      ( v6_lattices(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f56]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_1,plain,
% 27.59/3.99      ( v8_lattices(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f57]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_370,plain,
% 27.59/3.99      ( r1_lattices(X0,X1,X2)
% 27.59/3.99      | ~ r3_lattices(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_366,c_2,c_1]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_607,plain,
% 27.59/3.99      ( r1_lattices(X0,X1,X2)
% 27.59/3.99      | ~ r3_lattices(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_370,c_32]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_608,plain,
% 27.59/3.99      ( r1_lattices(sK4,X0,X1)
% 27.59/3.99      | ~ r3_lattices(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4)
% 27.59/3.99      | v2_struct_0(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_607]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_612,plain,
% 27.59/3.99      ( r1_lattices(sK4,X0,X1)
% 27.59/3.99      | ~ r3_lattices(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_608,c_33,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_661,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0,sK6)
% 27.59/3.99      | r1_lattices(sK4,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 27.59/3.99      | X1 != X0
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5
% 27.59/3.99      | sK5 != X2
% 27.59/3.99      | sK4 != sK4 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_27,c_612]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_662,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0,sK6)
% 27.59/3.99      | r1_lattices(sK4,X0,sK5)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_661]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_29,negated_conjecture,
% 27.59/3.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(cnf_transformation,[],[f83]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_666,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | r1_lattices(sK4,X0,sK5)
% 27.59/3.99      | ~ r3_lattice3(sK4,X0,sK6)
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_662,c_29]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_667,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0,sK6)
% 27.59/3.99      | r1_lattices(sK4,X0,sK5)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_666]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2599,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0_53,sK6)
% 27.59/3.99      | r1_lattices(sK4,X0_53,sK5)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_667]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3097,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) = sK5
% 27.59/3.99      | r3_lattice3(sK4,X0_53,sK6) != iProver_top
% 27.59/3.99      | r1_lattices(sK4,X0_53,sK5) = iProver_top
% 27.59/3.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2599]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_14152,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK5) = iProver_top
% 27.59/3.99      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_13672,c_3097]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3559,plain,
% 27.59/3.99      ( X0_53 != X1_53 | X1_53 = X0_53 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_2612,c_2611]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4318,plain,
% 27.59/3.99      ( k16_lattice3(sK4,X0_54) = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_3559,c_2596]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2614,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0_53,X0_56)
% 27.59/3.99      | m1_subset_1(X1_53,X0_56)
% 27.59/3.99      | X1_53 != X0_53 ),
% 27.59/3.99      theory(equality) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3281,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(X1_53,u1_struct_0(sK4))
% 27.59/3.99      | X1_53 != X0_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2614]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4076,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,X0_54) != X0_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3281]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_8725,plain,
% 27.59/3.99      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,X0_54) != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4076]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_8726,plain,
% 27.59/3.99      ( k16_lattice3(sK4,X0_54) != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_8725]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18423,plain,
% 27.59/3.99      ( r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK5) = iProver_top
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5
% 27.59/3.99      | sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_14152,c_4318,c_8726]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18424,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK5) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_18423]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18429,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5
% 27.59/3.99      | r1_lattices(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK5) = iProver_top
% 27.59/3.99      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_2596,c_18424]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18567,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),sK6),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5
% 27.59/3.99      | r1_lattices(sK4,k16_lattice3(sK4,X0_54),sK5) = iProver_top
% 27.59/3.99      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_2596,c_18429]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5649,plain,
% 27.59/3.99      ( k16_lattice3(sK4,X0_54) = k16_lattice3(sK4,X0_54) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2611]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5650,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_5649]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5795,plain,
% 27.59/3.99      ( k16_lattice3(sK4,X0_54) != X0_53
% 27.59/3.99      | k16_lattice3(sK4,X0_54) = sK5
% 27.59/3.99      | sK5 != X0_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2612]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_8447,plain,
% 27.59/3.99      ( k16_lattice3(sK4,X0_54) != k16_lattice3(sK4,X0_54)
% 27.59/3.99      | k16_lattice3(sK4,X0_54) = sK5
% 27.59/3.99      | sK5 != k16_lattice3(sK4,X0_54) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_5795]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_8448,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) != k16_lattice3(sK4,sK6)
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5
% 27.59/3.99      | sK5 != k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_8447]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4314,plain,
% 27.59/3.99      ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | X0_53 = sK3(X0_53,sK4,X0_54) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_3559,c_2586]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4899,plain,
% 27.59/3.99      ( ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | X0_53 = X1_53
% 27.59/3.99      | X1_53 != sK3(X0_53,sK4,X0_54) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_4314,c_2612]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_28,negated_conjecture,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6) | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(cnf_transformation,[],[f84]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2607,negated_conjecture,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6) | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_28]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3557,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | X0_53 != sK5
% 27.59/3.99      | k16_lattice3(sK4,sK6) = X0_53 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_2612,c_2607]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_17952,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | X0_53 = k16_lattice3(sK4,sK6)
% 27.59/3.99      | sK3(X0_53,sK4,X0_54) != sK5 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_4899,c_3557]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18606,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | ~ r2_hidden(sK5,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | sK5 = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_17952,c_2586]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_20,plain,
% 27.59/3.99      ( ~ r3_lattice3(X0,X1,X2)
% 27.59/3.99      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f91]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_712,plain,
% 27.59/3.99      ( ~ r3_lattice3(X0,X1,X2)
% 27.59/3.99      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_713,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0,X1)
% 27.59/3.99      | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_712]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_717,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 27.59/3.99      | ~ r3_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_713,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_718,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0,X1)
% 27.59/3.99      | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_717]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2597,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_718]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2652,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | r2_hidden(sK5,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2597]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4320,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6) | sK5 = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_3559,c_2607]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4334,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | X0_53 != k16_lattice3(sK4,sK6)
% 27.59/3.99      | sK5 = X0_53 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_4320,c_2612]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5751,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5
% 27.59/3.99      | sK5 = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_4334,c_3557]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2624,plain,
% 27.59/3.99      ( sK5 = sK5 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2611]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4079,plain,
% 27.59/3.99      ( k16_lattice3(sK4,X0_54) != X0_53
% 27.59/3.99      | sK5 != X0_53
% 27.59/3.99      | sK5 = k16_lattice3(sK4,X0_54) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2612]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4080,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) != sK5
% 27.59/3.99      | sK5 = k16_lattice3(sK4,sK6)
% 27.59/3.99      | sK5 != sK5 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4079]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6616,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) != sK5 | sK5 = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_5751,c_2624,c_4080]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_12,plain,
% 27.59/3.99      ( r4_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f66]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_771,plain,
% 27.59/3.99      ( r4_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_12,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_772,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_771]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_776,plain,
% 27.59/3.99      ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | r4_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_772,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_777,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_776]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2594,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK1(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_777]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_9321,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2594]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_9323,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | m1_subset_1(sK1(sK4,sK5,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_9321]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5800,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK5,X0_54)
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,sK5,X0_54),sK5)
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2592]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_9330,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,sK5,a_2_1_lattice3(sK4,X0_54)),sK5)
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_5800]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_9334,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | ~ r1_lattices(sK4,sK1(sK4,sK5,a_2_1_lattice3(sK4,sK6)),sK5)
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_9330]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5744,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | sK5 = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_4334,c_2596]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5770,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | X0_53 != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | sK5 = X0_53 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_5744,c_2612]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_16517,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
% 27.59/3.99      | sK5 = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_5770,c_3557]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4319,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4318]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3586,plain,
% 27.59/3.99      ( X0_53 != X1_53
% 27.59/3.99      | X0_53 = k15_lattice3(sK4,X0_54)
% 27.59/3.99      | k15_lattice3(sK4,X0_54) != X1_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2612]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4466,plain,
% 27.59/3.99      ( X0_53 != X1_53
% 27.59/3.99      | X0_53 = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) != X1_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3586]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4467,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
% 27.59/3.99      | sK5 = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | sK5 != sK5 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4466]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_8724,plain,
% 27.59/3.99      ( k16_lattice3(sK4,X0_54) != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | sK5 = k16_lattice3(sK4,X0_54)
% 27.59/3.99      | sK5 != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4079]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_8730,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | sK5 = k16_lattice3(sK4,sK6)
% 27.59/3.99      | sK5 != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_8724]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_16859,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
% 27.59/3.99      | sK5 = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_16517,c_2624,c_4319,c_4467,c_8730]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_16,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 27.59/3.99      | ~ v4_lattice3(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | k15_lattice3(X0,X2) = X1 ),
% 27.59/3.99      inference(cnf_transformation,[],[f71]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_488,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | k15_lattice3(X0,X2) = X1
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_489,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4)
% 27.59/3.99      | v2_struct_0(sK4)
% 27.59/3.99      | ~ v10_lattices(sK4)
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_488]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_493,plain,
% 27.59/3.99      ( m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_489,c_33,c_32,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_494,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_493]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2603,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(sK2(sK4,X0_54,X0_53),u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X0_54) = X0_53 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_494]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_15,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ v4_lattice3(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | k15_lattice3(X0,X2) = X1 ),
% 27.59/3.99      inference(cnf_transformation,[],[f72]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_512,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | k15_lattice3(X0,X2) = X1
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_513,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4)
% 27.59/3.99      | v2_struct_0(sK4)
% 27.59/3.99      | ~ v10_lattices(sK4)
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_512]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_517,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 27.59/3.99      | ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_513,c_33,c_32,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_518,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_517]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2602,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r4_lattice3(sK4,sK2(sK4,X0_54,X0_53),X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X0_54) = X0_53 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_518]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | r1_lattices(X0,X3,X1)
% 27.59/3.99      | ~ r2_hidden(X3,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f65]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_744,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | r1_lattices(X0,X3,X1)
% 27.59/3.99      | ~ r2_hidden(X3,X2)
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_13,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_745,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | r1_lattices(sK4,X2,X0)
% 27.59/3.99      | ~ r2_hidden(X2,X1)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_744]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_749,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 27.59/3.99      | ~ r2_hidden(X2,X1)
% 27.59/3.99      | r1_lattices(sK4,X2,X0)
% 27.59/3.99      | ~ r4_lattice3(sK4,X0,X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_745,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_750,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | r1_lattices(sK4,X2,X0)
% 27.59/3.99      | ~ r2_hidden(X2,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_749]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2595,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r1_lattices(sK4,X1_53,X0_53)
% 27.59/3.99      | ~ r2_hidden(X1_53,X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_750]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4681,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r1_lattices(sK4,X1_53,sK2(sK4,X0_54,X0_53))
% 27.59/3.99      | ~ r2_hidden(X1_53,X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK2(sK4,X0_54,X0_53),u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X0_54) = X0_53 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_2602,c_2595]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4693,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | r1_lattices(sK4,X1_53,sK2(sK4,X0_54,X0_53))
% 27.59/3.99      | ~ r2_hidden(X1_53,X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X0_54) = X0_53 ),
% 27.59/3.99      inference(backward_subsumption_resolution,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_2603,c_4681]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_14,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ v4_lattice3(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | k15_lattice3(X0,X2) = X1 ),
% 27.59/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_536,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0,X1,X2)
% 27.59/3.99      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | k15_lattice3(X0,X2) = X1
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_537,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4)
% 27.59/3.99      | v2_struct_0(sK4)
% 27.59/3.99      | ~ v10_lattices(sK4)
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_536]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_541,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 27.59/3.99      | ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_537,c_33,c_32,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_542,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0,X1)
% 27.59/3.99      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X1) = X0 ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_541]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2601,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ r1_lattices(sK4,X0_53,sK2(sK4,X0_54,X0_53))
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X0_54) = X0_53 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_542]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13950,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ r2_hidden(X0_53,X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X0_54) = X0_53 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_4693,c_2601]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_17024,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | ~ r2_hidden(sK5,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 27.59/3.99      | sK5 = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_16859,c_13950]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4903,plain,
% 27.59/3.99      ( r3_lattice3(X0_55,X0_53,X0_54)
% 27.59/3.99      | ~ r3_lattice3(X0_55,sK3(X0_53,sK4,X1_54),X0_54)
% 27.59/3.99      | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X1_54)) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_4314,c_2615]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_21,plain,
% 27.59/3.99      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 27.59/3.99      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_694,plain,
% 27.59/3.99      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 27.59/3.99      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_695,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
% 27.59/3.99      | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 27.59/3.99      | ~ l3_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_694]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_699,plain,
% 27.59/3.99      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 27.59/3.99      | r3_lattice3(sK4,sK3(X0,sK4,X1),X1) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_695,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_700,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
% 27.59/3.99      | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_699]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2598,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK3(X0_53,sK4,X0_54),X0_54)
% 27.59/3.99      | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_700]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18136,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ r2_hidden(X0_53,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_4903,c_2598]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18453,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r3_lattice3(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),X0_54)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_18136,c_2593]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18588,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | r1_lattices(sK4,sK1(sK4,X0_53,a_2_1_lattice3(sK4,sK6)),sK5)
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK1(sK4,X0_53,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_18453,c_2599]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18590,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | r1_lattices(sK4,sK1(sK4,sK5,a_2_1_lattice3(sK4,sK6)),sK5)
% 27.59/3.99      | ~ m1_subset_1(sK1(sK4,sK5,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_18588]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18611,plain,
% 27.59/3.99      ( sK5 = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_18606,c_29,c_2652,c_4320,c_6616,c_9323,c_9334,c_17024,
% 27.59/3.99                 c_18590]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18742,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) = sK5 ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_18567,c_29,c_2652,c_4320,c_5650,c_6616,c_8448,c_9323,
% 27.59/3.99                 c_9334,c_17024,c_18590]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_26,negated_conjecture,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5 ),
% 27.59/3.99      inference(cnf_transformation,[],[f86]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2608,negated_conjecture,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_26]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3088,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) != sK5
% 27.59/3.99      | r3_lattice3(sK4,sK5,sK6) != iProver_top
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2608]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18745,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6) != iProver_top
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_18742,c_3088]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_38,plain,
% 27.59/3.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_25,negated_conjecture,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | r3_lattice3(sK4,sK7,sK6)
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5 ),
% 27.59/3.99      inference(cnf_transformation,[],[f87]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2609,negated_conjecture,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | r3_lattice3(sK4,sK7,sK6)
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_25]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2625,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) != sK5
% 27.59/3.99      | r3_lattice3(sK4,sK5,sK6) != iProver_top
% 27.59/3.99      | r3_lattice3(sK4,sK7,sK6) = iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2609]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2626,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) != sK5
% 27.59/3.99      | r3_lattice3(sK4,sK5,sK6) != iProver_top
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2608]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_24,negated_conjecture,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | ~ r3_lattices(sK4,sK7,sK5)
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5 ),
% 27.59/3.99      inference(cnf_transformation,[],[f88]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4,plain,
% 27.59/3.99      ( ~ r1_lattices(X0,X1,X2)
% 27.59/3.99      | r3_lattices(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ v6_lattices(X0)
% 27.59/3.99      | ~ v8_lattices(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v9_lattices(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f60]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_398,plain,
% 27.59/3.99      ( ~ r1_lattices(X0,X1,X2)
% 27.59/3.99      | r3_lattices(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ v6_lattices(X0)
% 27.59/3.99      | ~ v8_lattices(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0) ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_402,plain,
% 27.59/3.99      ( ~ r1_lattices(X0,X1,X2)
% 27.59/3.99      | r3_lattices(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_398,c_2,c_1]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_583,plain,
% 27.59/3.99      ( ~ r1_lattices(X0,X1,X2)
% 27.59/3.99      | r3_lattices(X0,X1,X2)
% 27.59/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_402,c_32]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_584,plain,
% 27.59/3.99      ( ~ r1_lattices(sK4,X0,X1)
% 27.59/3.99      | r3_lattices(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4)
% 27.59/3.99      | v2_struct_0(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_583]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_588,plain,
% 27.59/3.99      ( ~ r1_lattices(sK4,X0,X1)
% 27.59/3.99      | r3_lattices(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_584,c_33,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_644,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | ~ r1_lattices(sK4,X0,X1)
% 27.59/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5
% 27.59/3.99      | sK5 != X1
% 27.59/3.99      | sK7 != X0
% 27.59/3.99      | sK4 != sK4 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_24,c_588]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_645,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | ~ r1_lattices(sK4,sK7,sK5)
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5 ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_644]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_647,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | ~ r1_lattices(sK4,sK7,sK5)
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5 ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_645,c_29,c_26]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2600,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6)
% 27.59/3.99      | ~ r1_lattices(sK4,sK7,sK5)
% 27.59/3.99      | k16_lattice3(sK4,sK6) != sK5 ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_647]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2644,plain,
% 27.59/3.99      ( k16_lattice3(sK4,sK6) != sK5
% 27.59/3.99      | r3_lattice3(sK4,sK5,sK6) != iProver_top
% 27.59/3.99      | r1_lattices(sK4,sK7,sK5) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2600]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2654,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2596]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3555,plain,
% 27.59/3.99      ( X0_53 != k16_lattice3(sK4,X0_54)
% 27.59/3.99      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) = X0_53 ),
% 27.59/3.99      inference(resolution,[status(thm)],[c_2612,c_2596]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3556,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = sK5
% 27.59/3.99      | sK5 != k16_lattice3(sK4,sK6) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3555]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18,plain,
% 27.59/3.99      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 27.59/3.99      | ~ v4_lattice3(X0)
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0) ),
% 27.59/3.99      inference(cnf_transformation,[],[f90]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_446,plain,
% 27.59/3.99      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 27.59/3.99      | ~ l3_lattices(X0)
% 27.59/3.99      | v2_struct_0(X0)
% 27.59/3.99      | ~ v10_lattices(X0)
% 27.59/3.99      | sK4 != X0 ),
% 27.59/3.99      inference(resolution_lifted,[status(thm)],[c_18,c_31]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_447,plain,
% 27.59/3.99      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 27.59/3.99      | ~ l3_lattices(sK4)
% 27.59/3.99      | v2_struct_0(sK4)
% 27.59/3.99      | ~ v10_lattices(sK4) ),
% 27.59/3.99      inference(unflattening,[status(thm)],[c_446]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_451,plain,
% 27.59/3.99      ( ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 27.59/3.99      | r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_447,c_33,c_32,c_30]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_452,plain,
% 27.59/3.99      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(renaming,[status(thm)],[c_451]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2605,plain,
% 27.59/3.99      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54)
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(subtyping,[status(esa)],[c_452]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3848,plain,
% 27.59/3.99      ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2605]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3853,plain,
% 27.59/3.99      ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54)) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_3848]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3855,plain,
% 27.59/3.99      ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3853]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3490,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,X0_54) != X0_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3281]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4192,plain,
% 27.59/3.99      ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4))
% 27.59/3.99      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) != X0_53 ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3490]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4193,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) != X0_53
% 27.59/3.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) = iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_4192]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4195,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top
% 27.59/3.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4193]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4461,plain,
% 27.59/3.99      ( X0_53 != k16_lattice3(sK4,X0_54)
% 27.59/3.99      | X0_53 = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) != k16_lattice3(sK4,X0_54) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3586]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4462,plain,
% 27.59/3.99      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != k16_lattice3(sK4,sK6)
% 27.59/3.99      | sK5 != k16_lattice3(sK4,sK6)
% 27.59/3.99      | sK5 = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4461]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_2617,plain,
% 27.59/3.99      ( ~ r4_lattice3(X0_55,X0_53,X0_54)
% 27.59/3.99      | r4_lattice3(X0_55,X1_53,X0_54)
% 27.59/3.99      | X1_53 != X0_53 ),
% 27.59/3.99      theory(equality) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3410,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,X0_54)
% 27.59/3.99      | ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54)
% 27.59/3.99      | X0_53 != k15_lattice3(sK4,X0_54) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2617]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5072,plain,
% 27.59/3.99      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | ~ r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | X0_53 != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3410]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5073,plain,
% 27.59/3.99      ( X0_53 != k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) = iProver_top
% 27.59/3.99      | r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_5072]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5075,plain,
% 27.59/3.99      ( sK5 != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | r4_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) != iProver_top
% 27.59/3.99      | r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6)) = iProver_top ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_5073]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_4948,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r1_lattices(sK4,X1_53,X0_53)
% 27.59/3.99      | ~ r2_hidden(X1_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2595]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5817,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | r1_lattices(sK4,sK7,sK5)
% 27.59/3.99      | ~ r2_hidden(sK7,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 27.59/3.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_4948]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5818,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | r1_lattices(sK4,sK7,sK5) = iProver_top
% 27.59/3.99      | r2_hidden(sK7,a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_5817]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5820,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6)) != iProver_top
% 27.59/3.99      | r1_lattices(sK4,sK7,sK5) = iProver_top
% 27.59/3.99      | r2_hidden(sK7,a_2_1_lattice3(sK4,sK6)) != iProver_top
% 27.59/3.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_5818]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13572,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK7,X0_54)
% 27.59/3.99      | r2_hidden(sK7,a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2597]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13573,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK7,X0_54) != iProver_top
% 27.59/3.99      | r2_hidden(sK7,a_2_1_lattice3(sK4,X0_54)) = iProver_top
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_13572]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13575,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK7,sK6) != iProver_top
% 27.59/3.99      | r2_hidden(sK7,a_2_1_lattice3(sK4,sK6)) = iProver_top
% 27.59/3.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_13573]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18785,plain,
% 27.59/3.99      ( r3_lattice3(sK4,sK5,sK6) != iProver_top ),
% 27.59/3.99      inference(global_propositional_subsumption,
% 27.59/3.99                [status(thm)],
% 27.59/3.99                [c_18745,c_29,c_38,c_2625,c_2626,c_2644,c_2652,c_2654,
% 27.59/3.99                 c_3556,c_3855,c_4195,c_4320,c_4462,c_5075,c_5650,c_5820,
% 27.59/3.99                 c_6616,c_8448,c_9323,c_9334,c_13575,c_17024,c_18590]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18787,plain,
% 27.59/3.99      ( ~ r3_lattice3(sK4,sK5,sK6) ),
% 27.59/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_18785]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3105,plain,
% 27.59/3.99      ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
% 27.59/3.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_2590]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6608,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54),u1_struct_0(sK4)) != iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_2596,c_6602]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_6701,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),a_2_1_lattice3(sK4,X0_54)) != iProver_top
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),X1_54) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_54)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_3105,c_6608]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18750,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,sK5,X0_54),a_2_1_lattice3(sK4,sK6)) != iProver_top
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),X0_54) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(superposition,[status(thm)],[c_18742,c_6701]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18768,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,sK0(sK4,sK5,X0_54),a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),X0_54)
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_18750]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18770,plain,
% 27.59/3.99      ( ~ r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK6)
% 27.59/3.99      | ~ m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_18768]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_18769,plain,
% 27.59/3.99      ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) != iProver_top
% 27.59/3.99      | r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK6) = iProver_top
% 27.59/3.99      | m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4)) != iProver_top ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_18750]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_3376,plain,
% 27.59/3.99      ( ~ r2_hidden(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54))
% 27.59/3.99      | sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54) = sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_2586]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13381,plain,
% 27.59/3.99      ( ~ r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54))
% 27.59/3.99      | sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54) = sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_3376]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13382,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54) = sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
% 27.59/3.99      | r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54)) != iProver_top ),
% 27.59/3.99      inference(predicate_to_equality,[status(thm)],[c_13381]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_13384,plain,
% 27.59/3.99      ( sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6) = sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
% 27.59/3.99      | r2_hidden(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) != iProver_top ),
% 27.59/3.99      inference(instantiation,[status(thm)],[c_13382]) ).
% 27.59/3.99  
% 27.59/3.99  cnf(c_5920,plain,
% 27.59/4.00      ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),X1_54)
% 27.59/4.00      | m1_subset_1(sK1(sK4,sK0(sK4,X0_53,X0_54),X1_54),u1_struct_0(sK4))
% 27.59/4.00      | ~ m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_2594]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_8034,plain,
% 27.59/4.00      ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
% 27.59/4.00      | m1_subset_1(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),u1_struct_0(sK4))
% 27.59/4.00      | ~ m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_5920]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_8037,plain,
% 27.59/4.00      ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
% 27.59/4.00      | m1_subset_1(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
% 27.59/4.00      | ~ m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_8034]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_3375,plain,
% 27.59/4.00      ( r3_lattice3(sK4,sK3(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),sK4,X0_54),X0_54)
% 27.59/4.00      | ~ r2_hidden(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_2598]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_6950,plain,
% 27.59/4.00      ( r3_lattice3(sK4,sK3(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),sK4,X1_54),X1_54)
% 27.59/4.00      | ~ r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_3375]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_6952,plain,
% 27.59/4.00      ( r3_lattice3(sK4,sK3(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),sK4,sK6),sK6)
% 27.59/4.00      | ~ r2_hidden(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_6950]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_5778,plain,
% 27.59/4.00      ( ~ r3_lattice3(X0_55,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),X0_54)
% 27.59/4.00      | r3_lattice3(X0_55,sK5,X0_54)
% 27.59/4.00      | r3_lattice3(sK4,sK5,sK6) ),
% 27.59/4.00      inference(resolution,[status(thm)],[c_5744,c_2615]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_5783,plain,
% 27.59/4.00      ( r3_lattice3(X0_55,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),X0_54) != iProver_top
% 27.59/4.00      | r3_lattice3(X0_55,sK5,X0_54) = iProver_top
% 27.59/4.00      | r3_lattice3(sK4,sK5,sK6) = iProver_top ),
% 27.59/4.00      inference(predicate_to_equality,[status(thm)],[c_5778]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_5785,plain,
% 27.59/4.00      ( r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK6) != iProver_top
% 27.59/4.00      | r3_lattice3(sK4,sK5,sK6) = iProver_top ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_5783]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_5784,plain,
% 27.59/4.00      ( ~ r3_lattice3(sK4,k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),sK6)
% 27.59/4.00      | r3_lattice3(sK4,sK5,sK6) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_5778]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_4194,plain,
% 27.59/4.00      ( m1_subset_1(k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)),u1_struct_0(sK4))
% 27.59/4.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 27.59/4.00      | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5 ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_4192]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_3374,plain,
% 27.59/4.00      ( r4_lattice3(sK4,X0_53,a_2_1_lattice3(sK4,X0_54))
% 27.59/4.00      | r2_hidden(sK1(sK4,X0_53,a_2_1_lattice3(sK4,X0_54)),a_2_1_lattice3(sK4,X0_54))
% 27.59/4.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_2593]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_3619,plain,
% 27.59/4.00      ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54))
% 27.59/4.00      | r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54))
% 27.59/4.00      | ~ m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_3374]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_3624,plain,
% 27.59/4.00      ( r4_lattice3(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)) = iProver_top
% 27.59/4.00      | r2_hidden(sK1(sK4,sK0(sK4,X0_53,X0_54),a_2_1_lattice3(sK4,X1_54)),a_2_1_lattice3(sK4,X1_54)) = iProver_top
% 27.59/4.00      | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) != iProver_top ),
% 27.59/4.00      inference(predicate_to_equality,[status(thm)],[c_3619]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_3626,plain,
% 27.59/4.00      ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)) = iProver_top
% 27.59/4.00      | r2_hidden(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6)) = iProver_top
% 27.59/4.00      | m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_3624]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_3625,plain,
% 27.59/4.00      ( r4_lattice3(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6))
% 27.59/4.00      | r2_hidden(sK1(sK4,sK0(sK4,sK5,sK6),a_2_1_lattice3(sK4,sK6)),a_2_1_lattice3(sK4,sK6))
% 27.59/4.00      | ~ m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_3619]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_7,plain,
% 27.59/4.00      ( r3_lattice3(X0,X1,X2)
% 27.59/4.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 27.59/4.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/4.00      | ~ l3_lattices(X0)
% 27.59/4.00      | v2_struct_0(X0) ),
% 27.59/4.00      inference(cnf_transformation,[],[f63]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_882,plain,
% 27.59/4.00      ( r3_lattice3(X0,X1,X2)
% 27.59/4.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 27.59/4.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.59/4.00      | ~ l3_lattices(X0)
% 27.59/4.00      | sK4 != X0 ),
% 27.59/4.00      inference(resolution_lifted,[status(thm)],[c_7,c_33]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_883,plain,
% 27.59/4.00      ( r3_lattice3(sK4,X0,X1)
% 27.59/4.00      | r2_hidden(sK0(sK4,X0,X1),X1)
% 27.59/4.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/4.00      | ~ l3_lattices(sK4) ),
% 27.59/4.00      inference(unflattening,[status(thm)],[c_882]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_887,plain,
% 27.59/4.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.59/4.00      | r2_hidden(sK0(sK4,X0,X1),X1)
% 27.59/4.00      | r3_lattice3(sK4,X0,X1) ),
% 27.59/4.00      inference(global_propositional_subsumption,
% 27.59/4.00                [status(thm)],
% 27.59/4.00                [c_883,c_30]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_888,plain,
% 27.59/4.00      ( r3_lattice3(sK4,X0,X1)
% 27.59/4.00      | r2_hidden(sK0(sK4,X0,X1),X1)
% 27.59/4.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 27.59/4.00      inference(renaming,[status(thm)],[c_887]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_2589,plain,
% 27.59/4.00      ( r3_lattice3(sK4,X0_53,X0_54)
% 27.59/4.00      | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54)
% 27.59/4.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 27.59/4.00      inference(subtyping,[status(esa)],[c_888]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_2674,plain,
% 27.59/4.00      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/4.00      | r2_hidden(sK0(sK4,sK5,sK6),sK6)
% 27.59/4.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_2589]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_2670,plain,
% 27.59/4.00      ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
% 27.59/4.00      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 27.59/4.00      | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 27.59/4.00      inference(predicate_to_equality,[status(thm)],[c_2590]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_2672,plain,
% 27.59/4.00      ( r3_lattice3(sK4,sK5,sK6) = iProver_top
% 27.59/4.00      | m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4)) = iProver_top
% 27.59/4.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_2670]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(c_2671,plain,
% 27.59/4.00      ( r3_lattice3(sK4,sK5,sK6)
% 27.59/4.00      | m1_subset_1(sK0(sK4,sK5,sK6),u1_struct_0(sK4))
% 27.59/4.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.59/4.00      inference(instantiation,[status(thm)],[c_2590]) ).
% 27.59/4.00  
% 27.59/4.00  cnf(contradiction,plain,
% 27.59/4.00      ( $false ),
% 27.59/4.00      inference(minisat,
% 27.59/4.00                [status(thm)],
% 27.59/4.00                [c_90004,c_77935,c_51151,c_25599,c_21160,c_18787,c_18785,
% 27.59/4.00                 c_18770,c_18769,c_18611,c_13384,c_8037,c_6952,c_5785,
% 27.59/4.00                 c_5784,c_4195,c_4194,c_3626,c_3625,c_3556,c_2674,c_2672,
% 27.59/4.00                 c_2671,c_38,c_29]) ).
% 27.59/4.00  
% 27.59/4.00  
% 27.59/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.59/4.00  
% 27.59/4.00  ------                               Statistics
% 27.59/4.00  
% 27.59/4.00  ------ Selected
% 27.59/4.00  
% 27.59/4.00  total_time:                             3.396
% 27.59/4.00  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:16 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 879 expanded)
%              Number of clauses        :  153 ( 245 expanded)
%              Number of leaves         :   17 ( 210 expanded)
%              Depth                    :   22
%              Number of atoms          : 1228 (5224 expanded)
%              Number of equality atoms :  124 ( 158 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r3_lattices(X0,k16_lattice3(X0,sK6),k16_lattice3(X0,sK5))
          | ~ r3_lattices(X0,k15_lattice3(X0,sK5),k15_lattice3(X0,sK6)) )
        & r1_tarski(sK5,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,X2),k16_lattice3(sK4,X1))
            | ~ r3_lattices(sK4,k15_lattice3(sK4,X1),k15_lattice3(sK4,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) )
    & r1_tarski(sK5,sK6)
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f58,f57])).

fof(f88,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f90,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
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

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f18])).

fof(f64,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r3_lattices(X0,X4,X1)
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_810,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_811,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_30,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_815,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_30])).

cnf(c_18,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_31,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_598,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_599,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_32,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_603,plain,
    ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_33,c_32,c_30])).

cnf(c_604,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_603])).

cnf(c_1008,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_815,c_604])).

cnf(c_1943,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1008])).

cnf(c_2875,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54)
    | r1_lattices(sK4,k15_lattice3(sK4,X1_54),k15_lattice3(sK4,X0_54))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_5674,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
    | r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2875])).

cnf(c_1952,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_815])).

cnf(c_4921,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_873,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_874,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_873])).

cnf(c_878,plain,
    ( r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_874,c_30])).

cnf(c_879,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_878])).

cnf(c_1949,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_879])).

cnf(c_2465,plain,
    ( r4_lattice3(sK4,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_380,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK5 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_29])).

cnf(c_381,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_1965,plain,
    ( ~ r2_hidden(X0_53,sK5)
    | r2_hidden(X0_53,sK6) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_2449,plain,
    ( r2_hidden(X0_53,sK5) != iProver_top
    | r2_hidden(X0_53,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1965])).

cnf(c_3332,plain,
    ( r4_lattice3(sK4,X0_53,sK5) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(sK4,X0_53,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2465,c_2449])).

cnf(c_19,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_211,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_20])).

cnf(c_475,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_31])).

cnf(c_476,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_480,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_33,c_32,c_30])).

cnf(c_1964,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_480])).

cnf(c_2450,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1964])).

cnf(c_2462,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1952])).

cnf(c_14,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_825,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_33])).

cnf(c_826,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_830,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_30])).

cnf(c_831,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1) ),
    inference(renaming,[status(thm)],[c_830])).

cnf(c_1951,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X1_53,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ r2_hidden(X1_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_831])).

cnf(c_2463,plain,
    ( r4_lattice3(sK4,X0_53,X0_54) != iProver_top
    | r1_lattices(sK4,X1_53,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1_53,X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(c_3521,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54) != iProver_top
    | r1_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_53,X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2462,c_2463])).

cnf(c_4208,plain,
    ( r1_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_3521])).

cnf(c_11,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_894,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_33])).

cnf(c_895,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_899,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_895,c_30])).

cnf(c_900,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_899])).

cnf(c_1948,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_900])).

cnf(c_2466,plain,
    ( r4_lattice3(sK4,X0_53,X0_54) = iProver_top
    | r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1948])).

cnf(c_4235,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_4208,c_2466])).

cnf(c_2024,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1952])).

cnf(c_13,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_852,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_853,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_857,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_853,c_30])).

cnf(c_858,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_857])).

cnf(c_1950,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_858])).

cnf(c_2682,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54)
    | m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1950])).

cnf(c_2683,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2682])).

cnf(c_4657,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54) = iProver_top
    | r2_hidden(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4235,c_2024,c_2683])).

cnf(c_4664,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3332,c_4657])).

cnf(c_4829,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4664,c_2462])).

cnf(c_4830,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4829])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_963,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_964,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_963])).

cnf(c_968,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_964,c_30])).

cnf(c_969,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_968])).

cnf(c_1945,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_969])).

cnf(c_2469,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1945])).

cnf(c_3344,plain,
    ( r3_lattice3(sK4,X0_53,sK5) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,X0_53,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_2449])).

cnf(c_26,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_21,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_194,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_21])).

cnf(c_490,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_31])).

cnf(c_491,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_495,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_33,c_32,c_30])).

cnf(c_1963,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_2451,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1963])).

cnf(c_795,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_796,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_800,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_796,c_30])).

cnf(c_1953,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_800])).

cnf(c_2461,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1953])).

cnf(c_10,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_915,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_33])).

cnf(c_916,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_920,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,X0,X2)
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_916,c_30])).

cnf(c_921,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1) ),
    inference(renaming,[status(thm)],[c_920])).

cnf(c_1947,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ r2_hidden(X1_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_921])).

cnf(c_2467,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) != iProver_top
    | r1_lattices(sK4,X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1_53,X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1947])).

cnf(c_3570,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) != iProver_top
    | r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_53,X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_2467])).

cnf(c_4451,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2451,c_3570])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_984,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_985,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_984])).

cnf(c_989,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_985,c_30])).

cnf(c_990,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_989])).

cnf(c_1944,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_990])).

cnf(c_2470,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
    | r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_4459,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_4451,c_2470])).

cnf(c_2021,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1953])).

cnf(c_9,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_942,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_33])).

cnf(c_943,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_947,plain,
    ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_30])).

cnf(c_948,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_947])).

cnf(c_1946,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_948])).

cnf(c_2679,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54)
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_2680,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2679])).

cnf(c_4671,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) = iProver_top
    | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4459,c_2021,c_2680])).

cnf(c_4678,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_4671])).

cnf(c_4683,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4678])).

cnf(c_1,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_427,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_431,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_3,c_2])).

cnf(c_737,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_431,c_32])).

cnf(c_738,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_742,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_738,c_33,c_30])).

cnf(c_743,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_742])).

cnf(c_1955,plain,
    ( ~ r1_lattices(sK4,X0_53,X1_53)
    | r3_lattices(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_743])).

cnf(c_2747,plain,
    ( ~ r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
    | r3_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_3149,plain,
    ( ~ r1_lattices(sK4,k15_lattice3(sK4,X0_54),k15_lattice3(sK4,X1_54))
    | r3_lattices(sK4,k15_lattice3(sK4,X0_54),k15_lattice3(sK4,X1_54))
    | ~ m1_subset_1(k15_lattice3(sK4,X1_54),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2747])).

cnf(c_4433,plain,
    ( ~ r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
    | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
    | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3149])).

cnf(c_3953,plain,
    ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_25,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_27,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ r3_lattice3(X0,X1,X2)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_27])).

cnf(c_202,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_505,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_202,c_31])).

cnf(c_506,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_33,c_32,c_30])).

cnf(c_511,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_510])).

cnf(c_1962,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r3_lattices(sK4,X0_53,k16_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_511])).

cnf(c_2452,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) != iProver_top
    | r3_lattices(sK4,X0_53,k16_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1962])).

cnf(c_28,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1966,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2448,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) != iProver_top
    | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1966])).

cnf(c_3103,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_2448])).

cnf(c_3104,plain,
    ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3103])).

cnf(c_2025,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5674,c_4921,c_4830,c_4683,c_4433,c_3953,c_3104,c_2025])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:54:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.45/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.02  
% 2.45/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.02  
% 2.45/1.02  ------  iProver source info
% 2.45/1.02  
% 2.45/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.02  git: non_committed_changes: false
% 2.45/1.02  git: last_make_outside_of_git: false
% 2.45/1.02  
% 2.45/1.02  ------ 
% 2.45/1.02  
% 2.45/1.02  ------ Input Options
% 2.45/1.02  
% 2.45/1.02  --out_options                           all
% 2.45/1.02  --tptp_safe_out                         true
% 2.45/1.02  --problem_path                          ""
% 2.45/1.02  --include_path                          ""
% 2.45/1.02  --clausifier                            res/vclausify_rel
% 2.45/1.02  --clausifier_options                    --mode clausify
% 2.45/1.02  --stdin                                 false
% 2.45/1.02  --stats_out                             all
% 2.45/1.02  
% 2.45/1.02  ------ General Options
% 2.45/1.02  
% 2.45/1.02  --fof                                   false
% 2.45/1.02  --time_out_real                         305.
% 2.45/1.02  --time_out_virtual                      -1.
% 2.45/1.02  --symbol_type_check                     false
% 2.45/1.02  --clausify_out                          false
% 2.45/1.02  --sig_cnt_out                           false
% 2.45/1.02  --trig_cnt_out                          false
% 2.45/1.02  --trig_cnt_out_tolerance                1.
% 2.45/1.02  --trig_cnt_out_sk_spl                   false
% 2.45/1.02  --abstr_cl_out                          false
% 2.45/1.02  
% 2.45/1.02  ------ Global Options
% 2.45/1.02  
% 2.45/1.02  --schedule                              default
% 2.45/1.02  --add_important_lit                     false
% 2.45/1.02  --prop_solver_per_cl                    1000
% 2.45/1.02  --min_unsat_core                        false
% 2.45/1.02  --soft_assumptions                      false
% 2.45/1.02  --soft_lemma_size                       3
% 2.45/1.02  --prop_impl_unit_size                   0
% 2.45/1.02  --prop_impl_unit                        []
% 2.45/1.02  --share_sel_clauses                     true
% 2.45/1.02  --reset_solvers                         false
% 2.45/1.02  --bc_imp_inh                            [conj_cone]
% 2.45/1.02  --conj_cone_tolerance                   3.
% 2.45/1.02  --extra_neg_conj                        none
% 2.45/1.02  --large_theory_mode                     true
% 2.45/1.02  --prolific_symb_bound                   200
% 2.45/1.02  --lt_threshold                          2000
% 2.45/1.02  --clause_weak_htbl                      true
% 2.45/1.02  --gc_record_bc_elim                     false
% 2.45/1.02  
% 2.45/1.02  ------ Preprocessing Options
% 2.45/1.02  
% 2.45/1.02  --preprocessing_flag                    true
% 2.45/1.02  --time_out_prep_mult                    0.1
% 2.45/1.02  --splitting_mode                        input
% 2.45/1.02  --splitting_grd                         true
% 2.45/1.02  --splitting_cvd                         false
% 2.45/1.02  --splitting_cvd_svl                     false
% 2.45/1.02  --splitting_nvd                         32
% 2.45/1.02  --sub_typing                            true
% 2.45/1.02  --prep_gs_sim                           true
% 2.45/1.02  --prep_unflatten                        true
% 2.45/1.02  --prep_res_sim                          true
% 2.45/1.02  --prep_upred                            true
% 2.45/1.02  --prep_sem_filter                       exhaustive
% 2.45/1.02  --prep_sem_filter_out                   false
% 2.45/1.02  --pred_elim                             true
% 2.45/1.02  --res_sim_input                         true
% 2.45/1.02  --eq_ax_congr_red                       true
% 2.45/1.02  --pure_diseq_elim                       true
% 2.45/1.02  --brand_transform                       false
% 2.45/1.02  --non_eq_to_eq                          false
% 2.45/1.02  --prep_def_merge                        true
% 2.45/1.02  --prep_def_merge_prop_impl              false
% 2.45/1.03  --prep_def_merge_mbd                    true
% 2.45/1.03  --prep_def_merge_tr_red                 false
% 2.45/1.03  --prep_def_merge_tr_cl                  false
% 2.45/1.03  --smt_preprocessing                     true
% 2.45/1.03  --smt_ac_axioms                         fast
% 2.45/1.03  --preprocessed_out                      false
% 2.45/1.03  --preprocessed_stats                    false
% 2.45/1.03  
% 2.45/1.03  ------ Abstraction refinement Options
% 2.45/1.03  
% 2.45/1.03  --abstr_ref                             []
% 2.45/1.03  --abstr_ref_prep                        false
% 2.45/1.03  --abstr_ref_until_sat                   false
% 2.45/1.03  --abstr_ref_sig_restrict                funpre
% 2.45/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.03  --abstr_ref_under                       []
% 2.45/1.03  
% 2.45/1.03  ------ SAT Options
% 2.45/1.03  
% 2.45/1.03  --sat_mode                              false
% 2.45/1.03  --sat_fm_restart_options                ""
% 2.45/1.03  --sat_gr_def                            false
% 2.45/1.03  --sat_epr_types                         true
% 2.45/1.03  --sat_non_cyclic_types                  false
% 2.45/1.03  --sat_finite_models                     false
% 2.45/1.03  --sat_fm_lemmas                         false
% 2.45/1.03  --sat_fm_prep                           false
% 2.45/1.03  --sat_fm_uc_incr                        true
% 2.45/1.03  --sat_out_model                         small
% 2.45/1.03  --sat_out_clauses                       false
% 2.45/1.03  
% 2.45/1.03  ------ QBF Options
% 2.45/1.03  
% 2.45/1.03  --qbf_mode                              false
% 2.45/1.03  --qbf_elim_univ                         false
% 2.45/1.03  --qbf_dom_inst                          none
% 2.45/1.03  --qbf_dom_pre_inst                      false
% 2.45/1.03  --qbf_sk_in                             false
% 2.45/1.03  --qbf_pred_elim                         true
% 2.45/1.03  --qbf_split                             512
% 2.45/1.03  
% 2.45/1.03  ------ BMC1 Options
% 2.45/1.03  
% 2.45/1.03  --bmc1_incremental                      false
% 2.45/1.03  --bmc1_axioms                           reachable_all
% 2.45/1.03  --bmc1_min_bound                        0
% 2.45/1.03  --bmc1_max_bound                        -1
% 2.45/1.03  --bmc1_max_bound_default                -1
% 2.45/1.03  --bmc1_symbol_reachability              true
% 2.45/1.03  --bmc1_property_lemmas                  false
% 2.45/1.03  --bmc1_k_induction                      false
% 2.45/1.03  --bmc1_non_equiv_states                 false
% 2.45/1.03  --bmc1_deadlock                         false
% 2.45/1.03  --bmc1_ucm                              false
% 2.45/1.03  --bmc1_add_unsat_core                   none
% 2.45/1.03  --bmc1_unsat_core_children              false
% 2.45/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.03  --bmc1_out_stat                         full
% 2.45/1.03  --bmc1_ground_init                      false
% 2.45/1.03  --bmc1_pre_inst_next_state              false
% 2.45/1.03  --bmc1_pre_inst_state                   false
% 2.45/1.03  --bmc1_pre_inst_reach_state             false
% 2.45/1.03  --bmc1_out_unsat_core                   false
% 2.45/1.03  --bmc1_aig_witness_out                  false
% 2.45/1.03  --bmc1_verbose                          false
% 2.45/1.03  --bmc1_dump_clauses_tptp                false
% 2.45/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.03  --bmc1_dump_file                        -
% 2.45/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.03  --bmc1_ucm_extend_mode                  1
% 2.45/1.03  --bmc1_ucm_init_mode                    2
% 2.45/1.03  --bmc1_ucm_cone_mode                    none
% 2.45/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.03  --bmc1_ucm_relax_model                  4
% 2.45/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.03  --bmc1_ucm_layered_model                none
% 2.45/1.03  --bmc1_ucm_max_lemma_size               10
% 2.45/1.03  
% 2.45/1.03  ------ AIG Options
% 2.45/1.03  
% 2.45/1.03  --aig_mode                              false
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation Options
% 2.45/1.03  
% 2.45/1.03  --instantiation_flag                    true
% 2.45/1.03  --inst_sos_flag                         false
% 2.45/1.03  --inst_sos_phase                        true
% 2.45/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel_side                     num_symb
% 2.45/1.03  --inst_solver_per_active                1400
% 2.45/1.03  --inst_solver_calls_frac                1.
% 2.45/1.03  --inst_passive_queue_type               priority_queues
% 2.45/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.03  --inst_passive_queues_freq              [25;2]
% 2.45/1.03  --inst_dismatching                      true
% 2.45/1.03  --inst_eager_unprocessed_to_passive     true
% 2.45/1.03  --inst_prop_sim_given                   true
% 2.45/1.03  --inst_prop_sim_new                     false
% 2.45/1.03  --inst_subs_new                         false
% 2.45/1.03  --inst_eq_res_simp                      false
% 2.45/1.03  --inst_subs_given                       false
% 2.45/1.03  --inst_orphan_elimination               true
% 2.45/1.03  --inst_learning_loop_flag               true
% 2.45/1.03  --inst_learning_start                   3000
% 2.45/1.03  --inst_learning_factor                  2
% 2.45/1.03  --inst_start_prop_sim_after_learn       3
% 2.45/1.03  --inst_sel_renew                        solver
% 2.45/1.03  --inst_lit_activity_flag                true
% 2.45/1.03  --inst_restr_to_given                   false
% 2.45/1.03  --inst_activity_threshold               500
% 2.45/1.03  --inst_out_proof                        true
% 2.45/1.03  
% 2.45/1.03  ------ Resolution Options
% 2.45/1.03  
% 2.45/1.03  --resolution_flag                       true
% 2.45/1.03  --res_lit_sel                           adaptive
% 2.45/1.03  --res_lit_sel_side                      none
% 2.45/1.03  --res_ordering                          kbo
% 2.45/1.03  --res_to_prop_solver                    active
% 2.45/1.03  --res_prop_simpl_new                    false
% 2.45/1.03  --res_prop_simpl_given                  true
% 2.45/1.03  --res_passive_queue_type                priority_queues
% 2.45/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.03  --res_passive_queues_freq               [15;5]
% 2.45/1.03  --res_forward_subs                      full
% 2.45/1.03  --res_backward_subs                     full
% 2.45/1.03  --res_forward_subs_resolution           true
% 2.45/1.03  --res_backward_subs_resolution          true
% 2.45/1.03  --res_orphan_elimination                true
% 2.45/1.03  --res_time_limit                        2.
% 2.45/1.03  --res_out_proof                         true
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Options
% 2.45/1.03  
% 2.45/1.03  --superposition_flag                    true
% 2.45/1.03  --sup_passive_queue_type                priority_queues
% 2.45/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.03  --demod_completeness_check              fast
% 2.45/1.03  --demod_use_ground                      true
% 2.45/1.03  --sup_to_prop_solver                    passive
% 2.45/1.03  --sup_prop_simpl_new                    true
% 2.45/1.03  --sup_prop_simpl_given                  true
% 2.45/1.03  --sup_fun_splitting                     false
% 2.45/1.03  --sup_smt_interval                      50000
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Simplification Setup
% 2.45/1.03  
% 2.45/1.03  --sup_indices_passive                   []
% 2.45/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_full_bw                           [BwDemod]
% 2.45/1.03  --sup_immed_triv                        [TrivRules]
% 2.45/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_immed_bw_main                     []
% 2.45/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  
% 2.45/1.03  ------ Combination Options
% 2.45/1.03  
% 2.45/1.03  --comb_res_mult                         3
% 2.45/1.03  --comb_sup_mult                         2
% 2.45/1.03  --comb_inst_mult                        10
% 2.45/1.03  
% 2.45/1.03  ------ Debug Options
% 2.45/1.03  
% 2.45/1.03  --dbg_backtrace                         false
% 2.45/1.03  --dbg_dump_prop_clauses                 false
% 2.45/1.03  --dbg_dump_prop_clauses_file            -
% 2.45/1.03  --dbg_out_stat                          false
% 2.45/1.03  ------ Parsing...
% 2.45/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.03  ------ Proving...
% 2.45/1.03  ------ Problem Properties 
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  clauses                                 24
% 2.45/1.03  conjectures                             1
% 2.45/1.03  EPR                                     1
% 2.45/1.03  Horn                                    16
% 2.45/1.03  unary                                   4
% 2.45/1.03  binary                                  2
% 2.45/1.03  lits                                    74
% 2.45/1.03  lits eq                                 6
% 2.45/1.03  fd_pure                                 0
% 2.45/1.03  fd_pseudo                               0
% 2.45/1.03  fd_cond                                 0
% 2.45/1.03  fd_pseudo_cond                          6
% 2.45/1.03  AC symbols                              0
% 2.45/1.03  
% 2.45/1.03  ------ Schedule dynamic 5 is on 
% 2.45/1.03  
% 2.45/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  ------ 
% 2.45/1.03  Current options:
% 2.45/1.03  ------ 
% 2.45/1.03  
% 2.45/1.03  ------ Input Options
% 2.45/1.03  
% 2.45/1.03  --out_options                           all
% 2.45/1.03  --tptp_safe_out                         true
% 2.45/1.03  --problem_path                          ""
% 2.45/1.03  --include_path                          ""
% 2.45/1.03  --clausifier                            res/vclausify_rel
% 2.45/1.03  --clausifier_options                    --mode clausify
% 2.45/1.03  --stdin                                 false
% 2.45/1.03  --stats_out                             all
% 2.45/1.03  
% 2.45/1.03  ------ General Options
% 2.45/1.03  
% 2.45/1.03  --fof                                   false
% 2.45/1.03  --time_out_real                         305.
% 2.45/1.03  --time_out_virtual                      -1.
% 2.45/1.03  --symbol_type_check                     false
% 2.45/1.03  --clausify_out                          false
% 2.45/1.03  --sig_cnt_out                           false
% 2.45/1.03  --trig_cnt_out                          false
% 2.45/1.03  --trig_cnt_out_tolerance                1.
% 2.45/1.03  --trig_cnt_out_sk_spl                   false
% 2.45/1.03  --abstr_cl_out                          false
% 2.45/1.03  
% 2.45/1.03  ------ Global Options
% 2.45/1.03  
% 2.45/1.03  --schedule                              default
% 2.45/1.03  --add_important_lit                     false
% 2.45/1.03  --prop_solver_per_cl                    1000
% 2.45/1.03  --min_unsat_core                        false
% 2.45/1.03  --soft_assumptions                      false
% 2.45/1.03  --soft_lemma_size                       3
% 2.45/1.03  --prop_impl_unit_size                   0
% 2.45/1.03  --prop_impl_unit                        []
% 2.45/1.03  --share_sel_clauses                     true
% 2.45/1.03  --reset_solvers                         false
% 2.45/1.03  --bc_imp_inh                            [conj_cone]
% 2.45/1.03  --conj_cone_tolerance                   3.
% 2.45/1.03  --extra_neg_conj                        none
% 2.45/1.03  --large_theory_mode                     true
% 2.45/1.03  --prolific_symb_bound                   200
% 2.45/1.03  --lt_threshold                          2000
% 2.45/1.03  --clause_weak_htbl                      true
% 2.45/1.03  --gc_record_bc_elim                     false
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing Options
% 2.45/1.03  
% 2.45/1.03  --preprocessing_flag                    true
% 2.45/1.03  --time_out_prep_mult                    0.1
% 2.45/1.03  --splitting_mode                        input
% 2.45/1.03  --splitting_grd                         true
% 2.45/1.03  --splitting_cvd                         false
% 2.45/1.03  --splitting_cvd_svl                     false
% 2.45/1.03  --splitting_nvd                         32
% 2.45/1.03  --sub_typing                            true
% 2.45/1.03  --prep_gs_sim                           true
% 2.45/1.03  --prep_unflatten                        true
% 2.45/1.03  --prep_res_sim                          true
% 2.45/1.03  --prep_upred                            true
% 2.45/1.03  --prep_sem_filter                       exhaustive
% 2.45/1.03  --prep_sem_filter_out                   false
% 2.45/1.03  --pred_elim                             true
% 2.45/1.03  --res_sim_input                         true
% 2.45/1.03  --eq_ax_congr_red                       true
% 2.45/1.03  --pure_diseq_elim                       true
% 2.45/1.03  --brand_transform                       false
% 2.45/1.03  --non_eq_to_eq                          false
% 2.45/1.03  --prep_def_merge                        true
% 2.45/1.03  --prep_def_merge_prop_impl              false
% 2.45/1.03  --prep_def_merge_mbd                    true
% 2.45/1.03  --prep_def_merge_tr_red                 false
% 2.45/1.03  --prep_def_merge_tr_cl                  false
% 2.45/1.03  --smt_preprocessing                     true
% 2.45/1.03  --smt_ac_axioms                         fast
% 2.45/1.03  --preprocessed_out                      false
% 2.45/1.03  --preprocessed_stats                    false
% 2.45/1.03  
% 2.45/1.03  ------ Abstraction refinement Options
% 2.45/1.03  
% 2.45/1.03  --abstr_ref                             []
% 2.45/1.03  --abstr_ref_prep                        false
% 2.45/1.03  --abstr_ref_until_sat                   false
% 2.45/1.03  --abstr_ref_sig_restrict                funpre
% 2.45/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.03  --abstr_ref_under                       []
% 2.45/1.03  
% 2.45/1.03  ------ SAT Options
% 2.45/1.03  
% 2.45/1.03  --sat_mode                              false
% 2.45/1.03  --sat_fm_restart_options                ""
% 2.45/1.03  --sat_gr_def                            false
% 2.45/1.03  --sat_epr_types                         true
% 2.45/1.03  --sat_non_cyclic_types                  false
% 2.45/1.03  --sat_finite_models                     false
% 2.45/1.03  --sat_fm_lemmas                         false
% 2.45/1.03  --sat_fm_prep                           false
% 2.45/1.03  --sat_fm_uc_incr                        true
% 2.45/1.03  --sat_out_model                         small
% 2.45/1.03  --sat_out_clauses                       false
% 2.45/1.03  
% 2.45/1.03  ------ QBF Options
% 2.45/1.03  
% 2.45/1.03  --qbf_mode                              false
% 2.45/1.03  --qbf_elim_univ                         false
% 2.45/1.03  --qbf_dom_inst                          none
% 2.45/1.03  --qbf_dom_pre_inst                      false
% 2.45/1.03  --qbf_sk_in                             false
% 2.45/1.03  --qbf_pred_elim                         true
% 2.45/1.03  --qbf_split                             512
% 2.45/1.03  
% 2.45/1.03  ------ BMC1 Options
% 2.45/1.03  
% 2.45/1.03  --bmc1_incremental                      false
% 2.45/1.03  --bmc1_axioms                           reachable_all
% 2.45/1.03  --bmc1_min_bound                        0
% 2.45/1.03  --bmc1_max_bound                        -1
% 2.45/1.03  --bmc1_max_bound_default                -1
% 2.45/1.03  --bmc1_symbol_reachability              true
% 2.45/1.03  --bmc1_property_lemmas                  false
% 2.45/1.03  --bmc1_k_induction                      false
% 2.45/1.03  --bmc1_non_equiv_states                 false
% 2.45/1.03  --bmc1_deadlock                         false
% 2.45/1.03  --bmc1_ucm                              false
% 2.45/1.03  --bmc1_add_unsat_core                   none
% 2.45/1.03  --bmc1_unsat_core_children              false
% 2.45/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.03  --bmc1_out_stat                         full
% 2.45/1.03  --bmc1_ground_init                      false
% 2.45/1.03  --bmc1_pre_inst_next_state              false
% 2.45/1.03  --bmc1_pre_inst_state                   false
% 2.45/1.03  --bmc1_pre_inst_reach_state             false
% 2.45/1.03  --bmc1_out_unsat_core                   false
% 2.45/1.03  --bmc1_aig_witness_out                  false
% 2.45/1.03  --bmc1_verbose                          false
% 2.45/1.03  --bmc1_dump_clauses_tptp                false
% 2.45/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.03  --bmc1_dump_file                        -
% 2.45/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.03  --bmc1_ucm_extend_mode                  1
% 2.45/1.03  --bmc1_ucm_init_mode                    2
% 2.45/1.03  --bmc1_ucm_cone_mode                    none
% 2.45/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.03  --bmc1_ucm_relax_model                  4
% 2.45/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.03  --bmc1_ucm_layered_model                none
% 2.45/1.03  --bmc1_ucm_max_lemma_size               10
% 2.45/1.03  
% 2.45/1.03  ------ AIG Options
% 2.45/1.03  
% 2.45/1.03  --aig_mode                              false
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation Options
% 2.45/1.03  
% 2.45/1.03  --instantiation_flag                    true
% 2.45/1.03  --inst_sos_flag                         false
% 2.45/1.03  --inst_sos_phase                        true
% 2.45/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel_side                     none
% 2.45/1.03  --inst_solver_per_active                1400
% 2.45/1.03  --inst_solver_calls_frac                1.
% 2.45/1.03  --inst_passive_queue_type               priority_queues
% 2.45/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.03  --inst_passive_queues_freq              [25;2]
% 2.45/1.03  --inst_dismatching                      true
% 2.45/1.03  --inst_eager_unprocessed_to_passive     true
% 2.45/1.03  --inst_prop_sim_given                   true
% 2.45/1.03  --inst_prop_sim_new                     false
% 2.45/1.03  --inst_subs_new                         false
% 2.45/1.03  --inst_eq_res_simp                      false
% 2.45/1.03  --inst_subs_given                       false
% 2.45/1.03  --inst_orphan_elimination               true
% 2.45/1.03  --inst_learning_loop_flag               true
% 2.45/1.03  --inst_learning_start                   3000
% 2.45/1.03  --inst_learning_factor                  2
% 2.45/1.03  --inst_start_prop_sim_after_learn       3
% 2.45/1.03  --inst_sel_renew                        solver
% 2.45/1.03  --inst_lit_activity_flag                true
% 2.45/1.03  --inst_restr_to_given                   false
% 2.45/1.03  --inst_activity_threshold               500
% 2.45/1.03  --inst_out_proof                        true
% 2.45/1.03  
% 2.45/1.03  ------ Resolution Options
% 2.45/1.03  
% 2.45/1.03  --resolution_flag                       false
% 2.45/1.03  --res_lit_sel                           adaptive
% 2.45/1.03  --res_lit_sel_side                      none
% 2.45/1.03  --res_ordering                          kbo
% 2.45/1.03  --res_to_prop_solver                    active
% 2.45/1.03  --res_prop_simpl_new                    false
% 2.45/1.03  --res_prop_simpl_given                  true
% 2.45/1.03  --res_passive_queue_type                priority_queues
% 2.45/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.03  --res_passive_queues_freq               [15;5]
% 2.45/1.03  --res_forward_subs                      full
% 2.45/1.03  --res_backward_subs                     full
% 2.45/1.03  --res_forward_subs_resolution           true
% 2.45/1.03  --res_backward_subs_resolution          true
% 2.45/1.03  --res_orphan_elimination                true
% 2.45/1.03  --res_time_limit                        2.
% 2.45/1.03  --res_out_proof                         true
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Options
% 2.45/1.03  
% 2.45/1.03  --superposition_flag                    true
% 2.45/1.03  --sup_passive_queue_type                priority_queues
% 2.45/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.03  --demod_completeness_check              fast
% 2.45/1.03  --demod_use_ground                      true
% 2.45/1.03  --sup_to_prop_solver                    passive
% 2.45/1.03  --sup_prop_simpl_new                    true
% 2.45/1.03  --sup_prop_simpl_given                  true
% 2.45/1.03  --sup_fun_splitting                     false
% 2.45/1.03  --sup_smt_interval                      50000
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Simplification Setup
% 2.45/1.03  
% 2.45/1.03  --sup_indices_passive                   []
% 2.45/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_full_bw                           [BwDemod]
% 2.45/1.03  --sup_immed_triv                        [TrivRules]
% 2.45/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_immed_bw_main                     []
% 2.45/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  
% 2.45/1.03  ------ Combination Options
% 2.45/1.03  
% 2.45/1.03  --comb_res_mult                         3
% 2.45/1.03  --comb_sup_mult                         2
% 2.45/1.03  --comb_inst_mult                        10
% 2.45/1.03  
% 2.45/1.03  ------ Debug Options
% 2.45/1.03  
% 2.45/1.03  --dbg_backtrace                         false
% 2.45/1.03  --dbg_dump_prop_clauses                 false
% 2.45/1.03  --dbg_dump_prop_clauses_file            -
% 2.45/1.03  --dbg_out_stat                          false
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  ------ Proving...
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  % SZS status Theorem for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  fof(f7,axiom,(
% 2.45/1.03    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f28,plain,(
% 2.45/1.03    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f7])).
% 2.45/1.03  
% 2.45/1.03  fof(f29,plain,(
% 2.45/1.03    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f28])).
% 2.45/1.03  
% 2.45/1.03  fof(f80,plain,(
% 2.45/1.03    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f29])).
% 2.45/1.03  
% 2.45/1.03  fof(f11,conjecture,(
% 2.45/1.03    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f12,negated_conjecture,(
% 2.45/1.03    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 2.45/1.03    inference(negated_conjecture,[],[f11])).
% 2.45/1.03  
% 2.45/1.03  fof(f36,plain,(
% 2.45/1.03    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f12])).
% 2.45/1.03  
% 2.45/1.03  fof(f37,plain,(
% 2.45/1.03    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f36])).
% 2.45/1.03  
% 2.45/1.03  fof(f58,plain,(
% 2.45/1.03    ( ! [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK6),k16_lattice3(X0,sK5)) | ~r3_lattices(X0,k15_lattice3(X0,sK5),k15_lattice3(X0,sK6))) & r1_tarski(sK5,sK6))) )),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f57,plain,(
% 2.45/1.03    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : ((~r3_lattices(sK4,k16_lattice3(sK4,X2),k16_lattice3(sK4,X1)) | ~r3_lattices(sK4,k15_lattice3(sK4,X1),k15_lattice3(sK4,X2))) & r1_tarski(X1,X2)) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f59,plain,(
% 2.45/1.03    ((~r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) | ~r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))) & r1_tarski(sK5,sK6)) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f58,f57])).
% 2.45/1.03  
% 2.45/1.03  fof(f88,plain,(
% 2.45/1.03    ~v2_struct_0(sK4)),
% 2.45/1.03    inference(cnf_transformation,[],[f59])).
% 2.45/1.03  
% 2.45/1.03  fof(f91,plain,(
% 2.45/1.03    l3_lattices(sK4)),
% 2.45/1.03    inference(cnf_transformation,[],[f59])).
% 2.45/1.03  
% 2.45/1.03  fof(f6,axiom,(
% 2.45/1.03    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f26,plain,(
% 2.45/1.03    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f6])).
% 2.45/1.03  
% 2.45/1.03  fof(f27,plain,(
% 2.45/1.03    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f26])).
% 2.45/1.03  
% 2.45/1.03  fof(f47,plain,(
% 2.45/1.03    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(nnf_transformation,[],[f27])).
% 2.45/1.03  
% 2.45/1.03  fof(f48,plain,(
% 2.45/1.03    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f47])).
% 2.45/1.03  
% 2.45/1.03  fof(f49,plain,(
% 2.45/1.03    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(rectify,[],[f48])).
% 2.45/1.03  
% 2.45/1.03  fof(f50,plain,(
% 2.45/1.03    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f51,plain,(
% 2.45/1.03    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 2.45/1.03  
% 2.45/1.03  fof(f76,plain,(
% 2.45/1.03    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f51])).
% 2.45/1.03  
% 2.45/1.03  fof(f94,plain,(
% 2.45/1.03    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(equality_resolution,[],[f76])).
% 2.45/1.03  
% 2.45/1.03  fof(f90,plain,(
% 2.45/1.03    v4_lattice3(sK4)),
% 2.45/1.03    inference(cnf_transformation,[],[f59])).
% 2.45/1.03  
% 2.45/1.03  fof(f89,plain,(
% 2.45/1.03    v10_lattices(sK4)),
% 2.45/1.03    inference(cnf_transformation,[],[f59])).
% 2.45/1.03  
% 2.45/1.03  fof(f5,axiom,(
% 2.45/1.03    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f24,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f5])).
% 2.45/1.03  
% 2.45/1.03  fof(f25,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f24])).
% 2.45/1.03  
% 2.45/1.03  fof(f43,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(nnf_transformation,[],[f25])).
% 2.45/1.03  
% 2.45/1.03  fof(f44,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(rectify,[],[f43])).
% 2.45/1.03  
% 2.45/1.03  fof(f45,plain,(
% 2.45/1.03    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f46,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 2.45/1.03  
% 2.45/1.03  fof(f73,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f46])).
% 2.45/1.03  
% 2.45/1.03  fof(f1,axiom,(
% 2.45/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f13,plain,(
% 2.45/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.45/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 2.45/1.03  
% 2.45/1.03  fof(f17,plain,(
% 2.45/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.45/1.03    inference(ennf_transformation,[],[f13])).
% 2.45/1.03  
% 2.45/1.03  fof(f60,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f17])).
% 2.45/1.03  
% 2.45/1.03  fof(f92,plain,(
% 2.45/1.03    r1_tarski(sK5,sK6)),
% 2.45/1.03    inference(cnf_transformation,[],[f59])).
% 2.45/1.03  
% 2.45/1.03  fof(f75,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f51])).
% 2.45/1.03  
% 2.45/1.03  fof(f95,plain,(
% 2.45/1.03    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(equality_resolution,[],[f75])).
% 2.45/1.03  
% 2.45/1.03  fof(f71,plain,(
% 2.45/1.03    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f46])).
% 2.45/1.03  
% 2.45/1.03  fof(f74,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f46])).
% 2.45/1.03  
% 2.45/1.03  fof(f72,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f46])).
% 2.45/1.03  
% 2.45/1.03  fof(f4,axiom,(
% 2.45/1.03    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f22,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f4])).
% 2.45/1.03  
% 2.45/1.03  fof(f23,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f22])).
% 2.45/1.03  
% 2.45/1.03  fof(f39,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(nnf_transformation,[],[f23])).
% 2.45/1.03  
% 2.45/1.03  fof(f40,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(rectify,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f41,plain,(
% 2.45/1.03    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f42,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.45/1.03  
% 2.45/1.03  fof(f69,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f42])).
% 2.45/1.03  
% 2.45/1.03  fof(f9,axiom,(
% 2.45/1.03    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f32,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f9])).
% 2.45/1.03  
% 2.45/1.03  fof(f33,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f32])).
% 2.45/1.03  
% 2.45/1.03  fof(f52,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(nnf_transformation,[],[f33])).
% 2.45/1.03  
% 2.45/1.03  fof(f53,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f52])).
% 2.45/1.03  
% 2.45/1.03  fof(f54,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(rectify,[],[f53])).
% 2.45/1.03  
% 2.45/1.03  fof(f55,plain,(
% 2.45/1.03    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f56,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 2.45/1.03  
% 2.45/1.03  fof(f82,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f56])).
% 2.45/1.03  
% 2.45/1.03  fof(f97,plain,(
% 2.45/1.03    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(equality_resolution,[],[f82])).
% 2.45/1.03  
% 2.45/1.03  fof(f8,axiom,(
% 2.45/1.03    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f30,plain,(
% 2.45/1.03    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f8])).
% 2.45/1.03  
% 2.45/1.03  fof(f31,plain,(
% 2.45/1.03    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f30])).
% 2.45/1.03  
% 2.45/1.03  fof(f81,plain,(
% 2.45/1.03    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f31])).
% 2.45/1.03  
% 2.45/1.03  fof(f67,plain,(
% 2.45/1.03    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f42])).
% 2.45/1.03  
% 2.45/1.03  fof(f70,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f42])).
% 2.45/1.03  
% 2.45/1.03  fof(f68,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f42])).
% 2.45/1.03  
% 2.45/1.03  fof(f2,axiom,(
% 2.45/1.03    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f14,plain,(
% 2.45/1.03    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.45/1.03    inference(pure_predicate_removal,[],[f2])).
% 2.45/1.03  
% 2.45/1.03  fof(f15,plain,(
% 2.45/1.03    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.45/1.03    inference(pure_predicate_removal,[],[f14])).
% 2.45/1.03  
% 2.45/1.03  fof(f16,plain,(
% 2.45/1.03    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 2.45/1.03    inference(pure_predicate_removal,[],[f15])).
% 2.45/1.03  
% 2.45/1.03  fof(f18,plain,(
% 2.45/1.03    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.45/1.03    inference(ennf_transformation,[],[f16])).
% 2.45/1.03  
% 2.45/1.03  fof(f19,plain,(
% 2.45/1.03    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.45/1.03    inference(flattening,[],[f18])).
% 2.45/1.03  
% 2.45/1.03  fof(f64,plain,(
% 2.45/1.03    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f19])).
% 2.45/1.03  
% 2.45/1.03  fof(f3,axiom,(
% 2.45/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f20,plain,(
% 2.45/1.03    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f3])).
% 2.45/1.03  
% 2.45/1.03  fof(f21,plain,(
% 2.45/1.03    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f20])).
% 2.45/1.03  
% 2.45/1.03  fof(f38,plain,(
% 2.45/1.03    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(nnf_transformation,[],[f21])).
% 2.45/1.03  
% 2.45/1.03  fof(f66,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f38])).
% 2.45/1.03  
% 2.45/1.03  fof(f62,plain,(
% 2.45/1.03    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f19])).
% 2.45/1.03  
% 2.45/1.03  fof(f63,plain,(
% 2.45/1.03    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f19])).
% 2.45/1.03  
% 2.45/1.03  fof(f83,plain,(
% 2.45/1.03    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f56])).
% 2.45/1.03  
% 2.45/1.03  fof(f96,plain,(
% 2.45/1.03    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(equality_resolution,[],[f83])).
% 2.45/1.03  
% 2.45/1.03  fof(f10,axiom,(
% 2.45/1.03    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 2.45/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f34,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f10])).
% 2.45/1.03  
% 2.45/1.03  fof(f35,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f34])).
% 2.45/1.03  
% 2.45/1.03  fof(f87,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f35])).
% 2.45/1.03  
% 2.45/1.03  fof(f93,plain,(
% 2.45/1.03    ~r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) | ~r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))),
% 2.45/1.03    inference(cnf_transformation,[],[f59])).
% 2.45/1.03  
% 2.45/1.03  cnf(c_20,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f80]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_33,negated_conjecture,
% 2.45/1.03      ( ~ v2_struct_0(sK4) ),
% 2.45/1.03      inference(cnf_transformation,[],[f88]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_810,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_811,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_810]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_30,negated_conjecture,
% 2.45/1.03      ( l3_lattices(sK4) ),
% 2.45/1.03      inference(cnf_transformation,[],[f91]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_815,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_811,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_18,plain,
% 2.45/1.03      ( ~ r4_lattice3(X0,X1,X2)
% 2.45/1.03      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f94]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_31,negated_conjecture,
% 2.45/1.03      ( v4_lattice3(sK4) ),
% 2.45/1.03      inference(cnf_transformation,[],[f90]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_598,plain,
% 2.45/1.03      ( ~ r4_lattice3(X0,X1,X2)
% 2.45/1.03      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_31]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_599,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4)
% 2.45/1.03      | v2_struct_0(sK4)
% 2.45/1.03      | ~ v10_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_598]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_32,negated_conjecture,
% 2.45/1.03      ( v10_lattices(sK4) ),
% 2.45/1.03      inference(cnf_transformation,[],[f89]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_603,plain,
% 2.45/1.03      ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 2.45/1.03      | ~ r4_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_599,c_33,c_32,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_604,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_603]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1008,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(backward_subsumption_resolution,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_815,c_604]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1943,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_1008]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2875,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54)
% 2.45/1.03      | r1_lattices(sK4,k15_lattice3(sK4,X1_54),k15_lattice3(sK4,X0_54))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1943]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_5674,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
% 2.45/1.03      | r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2875]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1952,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_815]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4921,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1952]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_12,plain,
% 2.45/1.03      ( r4_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_873,plain,
% 2.45/1.03      ( r4_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_874,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r2_hidden(sK1(sK4,X0,X1),X1)
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_873]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_878,plain,
% 2.45/1.03      ( r2_hidden(sK1(sK4,X0,X1),X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r4_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_874,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_879,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r2_hidden(sK1(sK4,X0,X1),X1) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_878]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1949,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.45/1.03      | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_879]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2465,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0_53,X0_54) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_0,plain,
% 2.45/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_29,negated_conjecture,
% 2.45/1.03      ( r1_tarski(sK5,sK6) ),
% 2.45/1.03      inference(cnf_transformation,[],[f92]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_380,plain,
% 2.45/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK5 != X1 | sK6 != X2 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_29]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_381,plain,
% 2.45/1.03      ( ~ r2_hidden(X0,sK5) | r2_hidden(X0,sK6) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_380]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1965,plain,
% 2.45/1.03      ( ~ r2_hidden(X0_53,sK5) | r2_hidden(X0_53,sK6) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_381]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2449,plain,
% 2.45/1.03      ( r2_hidden(X0_53,sK5) != iProver_top
% 2.45/1.03      | r2_hidden(X0_53,sK6) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1965]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3332,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0_53,sK5) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(sK1(sK4,X0_53,sK5),sK6) = iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_2465,c_2449]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_19,plain,
% 2.45/1.03      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f95]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_211,plain,
% 2.45/1.03      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_19,c_20]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_475,plain,
% 2.45/1.03      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_211,c_31]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_476,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 2.45/1.03      | ~ l3_lattices(sK4)
% 2.45/1.03      | v2_struct_0(sK4)
% 2.45/1.03      | ~ v10_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_475]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_480,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_476,c_33,c_32,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1964,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_480]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2450,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1964]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2462,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1952]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_14,plain,
% 2.45/1.03      ( ~ r4_lattice3(X0,X1,X2)
% 2.45/1.03      | r1_lattices(X0,X3,X1)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ r2_hidden(X3,X2)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_825,plain,
% 2.45/1.03      ( ~ r4_lattice3(X0,X1,X2)
% 2.45/1.03      | r1_lattices(X0,X3,X1)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ r2_hidden(X3,X2)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_826,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | r1_lattices(sK4,X2,X0)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.45/1.03      | ~ r2_hidden(X2,X1)
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_825]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_830,plain,
% 2.45/1.03      ( ~ r2_hidden(X2,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r1_lattices(sK4,X2,X0)
% 2.45/1.03      | ~ r4_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_826,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_831,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | r1_lattices(sK4,X2,X0)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.45/1.03      | ~ r2_hidden(X2,X1) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_830]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1951,plain,
% 2.45/1.03      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | r1_lattices(sK4,X1_53,X0_53)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
% 2.45/1.03      | ~ r2_hidden(X1_53,X0_54) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_831]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2463,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0_53,X0_54) != iProver_top
% 2.45/1.03      | r1_lattices(sK4,X1_53,X0_53) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(X1_53,X0_54) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1951]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3521,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54) != iProver_top
% 2.45/1.03      | r1_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54)) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(X0_53,X1_54) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_2462,c_2463]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4208,plain,
% 2.45/1.03      ( r1_lattices(sK4,X0_53,k15_lattice3(sK4,X0_54)) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(X0_53,X0_54) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_2450,c_3521]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_11,plain,
% 2.45/1.03      ( r4_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_894,plain,
% 2.45/1.03      ( r4_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_895,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_894]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_899,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 2.45/1.03      | r4_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_895,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_900,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_899]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1948,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | ~ r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_900]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2466,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0_53,X0_54) = iProver_top
% 2.45/1.03      | r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53) != iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1948]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4235,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54) = iProver_top
% 2.45/1.03      | m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),X0_54) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_4208,c_2466]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2024,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1952]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_13,plain,
% 2.45/1.03      ( r4_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_852,plain,
% 2.45/1.03      ( r4_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_853,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_852]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_857,plain,
% 2.45/1.03      ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r4_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_853,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_858,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_857]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1950,plain,
% 2.45/1.03      ( r4_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.45/1.03      | m1_subset_1(sK1(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_858]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2682,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54)
% 2.45/1.03      | m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1950]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2683,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54) = iProver_top
% 2.45/1.03      | m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4)) = iProver_top
% 2.45/1.03      | m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_2682]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4657,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X1_54) = iProver_top
% 2.45/1.03      | r2_hidden(sK1(sK4,k15_lattice3(sK4,X0_54),X1_54),X0_54) != iProver_top ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_4235,c_2024,c_2683]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4664,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) = iProver_top
% 2.45/1.03      | m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_3332,c_4657]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4829,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) = iProver_top ),
% 2.45/1.03      inference(forward_subsumption_resolution,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_4664,c_2462]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4830,plain,
% 2.45/1.03      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) ),
% 2.45/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_4829]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_8,plain,
% 2.45/1.03      ( r3_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_963,plain,
% 2.45/1.03      ( r3_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_964,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r2_hidden(sK0(sK4,X0,X1),X1)
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_963]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_968,plain,
% 2.45/1.03      ( r2_hidden(sK0(sK4,X0,X1),X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r3_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_964,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_969,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r2_hidden(sK0(sK4,X0,X1),X1) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_968]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1945,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.45/1.03      | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_969]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2469,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1945]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3344,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0_53,sK5) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(sK0(sK4,X0_53,sK5),sK6) = iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_2469,c_2449]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_26,plain,
% 2.45/1.03      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 2.45/1.03      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f97]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_21,plain,
% 2.45/1.03      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f81]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_194,plain,
% 2.45/1.03      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_26,c_21]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_490,plain,
% 2.45/1.03      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_194,c_31]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_491,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
% 2.45/1.03      | ~ l3_lattices(sK4)
% 2.45/1.03      | v2_struct_0(sK4)
% 2.45/1.03      | ~ v10_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_490]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_495,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_491,c_33,c_32,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1963,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_495]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2451,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1963]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_795,plain,
% 2.45/1.03      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_796,plain,
% 2.45/1.03      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_795]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_800,plain,
% 2.45/1.03      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_796,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1953,plain,
% 2.45/1.03      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_800]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2461,plain,
% 2.45/1.03      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1953]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_10,plain,
% 2.45/1.03      ( ~ r3_lattice3(X0,X1,X2)
% 2.45/1.03      | r1_lattices(X0,X1,X3)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ r2_hidden(X3,X2)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_915,plain,
% 2.45/1.03      ( ~ r3_lattice3(X0,X1,X2)
% 2.45/1.03      | r1_lattices(X0,X1,X3)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ r2_hidden(X3,X2)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_916,plain,
% 2.45/1.03      ( ~ r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | r1_lattices(sK4,X0,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.45/1.03      | ~ r2_hidden(X2,X1)
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_915]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_920,plain,
% 2.45/1.03      ( ~ r2_hidden(X2,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r1_lattices(sK4,X0,X2)
% 2.45/1.03      | ~ r3_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_916,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_921,plain,
% 2.45/1.03      ( ~ r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | r1_lattices(sK4,X0,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.45/1.03      | ~ r2_hidden(X2,X1) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_920]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1947,plain,
% 2.45/1.03      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | r1_lattices(sK4,X0_53,X1_53)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
% 2.45/1.03      | ~ r2_hidden(X1_53,X0_54) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_921]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2467,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0_53,X0_54) != iProver_top
% 2.45/1.03      | r1_lattices(sK4,X0_53,X1_53) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(X1_53,X0_54) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1947]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3570,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) != iProver_top
% 2.45/1.03      | r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(X0_53,X1_54) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_2461,c_2467]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4451,plain,
% 2.45/1.03      ( r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(X0_53,X0_54) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_2451,c_3570]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_7,plain,
% 2.45/1.03      ( r3_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_984,plain,
% 2.45/1.03      ( r3_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_985,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_984]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_989,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 2.45/1.03      | r3_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_985,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_990,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_989]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1944,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | ~ r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54))
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_990]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2470,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
% 2.45/1.03      | r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54)) != iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4459,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) = iProver_top
% 2.45/1.03      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top
% 2.45/1.03      | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),X0_54) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_4451,c_2470]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2021,plain,
% 2.45/1.03      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1953]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_9,plain,
% 2.45/1.03      ( r3_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_942,plain,
% 2.45/1.03      ( r3_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_943,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_942]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_947,plain,
% 2.45/1.03      ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r3_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_943,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_948,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_947]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1946,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.45/1.03      | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_948]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2679,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54)
% 2.45/1.03      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1946]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2680,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) = iProver_top
% 2.45/1.03      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),u1_struct_0(sK4)) = iProver_top
% 2.45/1.03      | m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_2679]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4671,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) = iProver_top
% 2.45/1.03      | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_54),X1_54),X0_54) != iProver_top ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_4459,c_2021,c_2680]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4678,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
% 2.45/1.03      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_3344,c_4671]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4683,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5)
% 2.45/1.03      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_4678]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1,plain,
% 2.45/1.03      ( ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0)
% 2.45/1.03      | v9_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_5,plain,
% 2.45/1.03      ( ~ r1_lattices(X0,X1,X2)
% 2.45/1.03      | r3_lattices(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ v6_lattices(X0)
% 2.45/1.03      | ~ v8_lattices(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v9_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_427,plain,
% 2.45/1.03      ( ~ r1_lattices(X0,X1,X2)
% 2.45/1.03      | r3_lattices(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ v6_lattices(X0)
% 2.45/1.03      | ~ v8_lattices(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(resolution,[status(thm)],[c_1,c_5]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3,plain,
% 2.45/1.03      ( v6_lattices(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2,plain,
% 2.45/1.03      ( v8_lattices(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_431,plain,
% 2.45/1.03      ( ~ r1_lattices(X0,X1,X2)
% 2.45/1.03      | r3_lattices(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_427,c_3,c_2]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_737,plain,
% 2.45/1.03      ( ~ r1_lattices(X0,X1,X2)
% 2.45/1.03      | r3_lattices(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_431,c_32]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_738,plain,
% 2.45/1.03      ( ~ r1_lattices(sK4,X0,X1)
% 2.45/1.03      | r3_lattices(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4)
% 2.45/1.03      | v2_struct_0(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_737]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_742,plain,
% 2.45/1.03      ( ~ r1_lattices(sK4,X0,X1)
% 2.45/1.03      | r3_lattices(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_738,c_33,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_743,plain,
% 2.45/1.03      ( ~ r1_lattices(sK4,X0,X1)
% 2.45/1.03      | r3_lattices(sK4,X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_742]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1955,plain,
% 2.45/1.03      ( ~ r1_lattices(sK4,X0_53,X1_53)
% 2.45/1.03      | r3_lattices(sK4,X0_53,X1_53)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_743]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2747,plain,
% 2.45/1.03      ( ~ r1_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
% 2.45/1.03      | r3_lattices(sK4,k15_lattice3(sK4,X0_54),X0_53)
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1955]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3149,plain,
% 2.45/1.03      ( ~ r1_lattices(sK4,k15_lattice3(sK4,X0_54),k15_lattice3(sK4,X1_54))
% 2.45/1.03      | r3_lattices(sK4,k15_lattice3(sK4,X0_54),k15_lattice3(sK4,X1_54))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,X1_54),u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2747]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4433,plain,
% 2.45/1.03      ( ~ r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
% 2.45/1.03      | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4))
% 2.45/1.03      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3149]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3953,plain,
% 2.45/1.03      ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1953]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_25,plain,
% 2.45/1.03      ( ~ r3_lattice3(X0,X1,X2)
% 2.45/1.03      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f96]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_27,plain,
% 2.45/1.03      ( ~ r3_lattice3(X0,X1,X2)
% 2.45/1.03      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f87]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_201,plain,
% 2.45/1.03      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 2.45/1.03      | ~ r3_lattice3(X0,X1,X2)
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_25,c_27]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_202,plain,
% 2.45/1.03      ( ~ r3_lattice3(X0,X1,X2)
% 2.45/1.03      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ v4_lattice3(X0)
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_201]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_505,plain,
% 2.45/1.03      ( ~ r3_lattice3(X0,X1,X2)
% 2.45/1.03      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.45/1.03      | ~ l3_lattices(X0)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v10_lattices(X0)
% 2.45/1.03      | sK4 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_202,c_31]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_506,plain,
% 2.45/1.03      ( ~ r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | ~ l3_lattices(sK4)
% 2.45/1.03      | v2_struct_0(sK4)
% 2.45/1.03      | ~ v10_lattices(sK4) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_505]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_510,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.45/1.03      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 2.45/1.03      | ~ r3_lattice3(sK4,X0,X1) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_506,c_33,c_32,c_30]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_511,plain,
% 2.45/1.03      ( ~ r3_lattice3(sK4,X0,X1)
% 2.45/1.03      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_510]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1962,plain,
% 2.45/1.03      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 2.45/1.03      | r3_lattices(sK4,X0_53,k16_lattice3(sK4,X0_54))
% 2.45/1.03      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_511]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2452,plain,
% 2.45/1.03      ( r3_lattice3(sK4,X0_53,X0_54) != iProver_top
% 2.45/1.03      | r3_lattices(sK4,X0_53,k16_lattice3(sK4,X0_54)) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1962]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_28,negated_conjecture,
% 2.45/1.03      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
% 2.45/1.03      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
% 2.45/1.03      inference(cnf_transformation,[],[f93]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1966,negated_conjecture,
% 2.45/1.03      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
% 2.45/1.03      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_28]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2448,plain,
% 2.45/1.03      ( r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) != iProver_top
% 2.45/1.03      | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1966]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3103,plain,
% 2.45/1.03      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 2.45/1.03      | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top
% 2.45/1.03      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_2452,c_2448]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3104,plain,
% 2.45/1.03      ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5)
% 2.45/1.03      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
% 2.45/1.03      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3103]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2025,plain,
% 2.45/1.03      ( m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1952]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(contradiction,plain,
% 2.45/1.03      ( $false ),
% 2.45/1.03      inference(minisat,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_5674,c_4921,c_4830,c_4683,c_4433,c_3953,c_3104,c_2025]) ).
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  ------                               Statistics
% 2.45/1.03  
% 2.45/1.03  ------ General
% 2.45/1.03  
% 2.45/1.03  abstr_ref_over_cycles:                  0
% 2.45/1.03  abstr_ref_under_cycles:                 0
% 2.45/1.03  gc_basic_clause_elim:                   0
% 2.45/1.03  forced_gc_time:                         0
% 2.45/1.03  parsing_time:                           0.01
% 2.45/1.03  unif_index_cands_time:                  0.
% 2.45/1.03  unif_index_add_time:                    0.
% 2.45/1.03  orderings_time:                         0.
% 2.45/1.03  out_proof_time:                         0.016
% 2.45/1.03  total_time:                             0.164
% 2.45/1.03  num_of_symbols:                         56
% 2.45/1.03  num_of_terms:                           4742
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing
% 2.45/1.03  
% 2.45/1.03  num_of_splits:                          0
% 2.45/1.03  num_of_split_atoms:                     0
% 2.45/1.03  num_of_reused_defs:                     0
% 2.45/1.03  num_eq_ax_congr_red:                    57
% 2.45/1.03  num_of_sem_filtered_clauses:            1
% 2.45/1.03  num_of_subtypes:                        4
% 2.45/1.03  monotx_restored_types:                  0
% 2.45/1.03  sat_num_of_epr_types:                   0
% 2.45/1.03  sat_num_of_non_cyclic_types:            0
% 2.45/1.03  sat_guarded_non_collapsed_types:        1
% 2.45/1.03  num_pure_diseq_elim:                    0
% 2.45/1.03  simp_replaced_by:                       0
% 2.45/1.03  res_preprocessed:                       121
% 2.45/1.03  prep_upred:                             0
% 2.45/1.03  prep_unflattend:                        82
% 2.45/1.03  smt_new_axioms:                         0
% 2.45/1.03  pred_elim_cands:                        6
% 2.45/1.03  pred_elim:                              8
% 2.45/1.03  pred_elim_cl:                           8
% 2.45/1.03  pred_elim_cycles:                       10
% 2.45/1.03  merged_defs:                            0
% 2.45/1.03  merged_defs_ncl:                        0
% 2.45/1.03  bin_hyper_res:                          0
% 2.45/1.03  prep_cycles:                            4
% 2.45/1.03  pred_elim_time:                         0.017
% 2.45/1.03  splitting_time:                         0.
% 2.45/1.03  sem_filter_time:                        0.
% 2.45/1.03  monotx_time:                            0.
% 2.45/1.03  subtype_inf_time:                       0.
% 2.45/1.03  
% 2.45/1.03  ------ Problem properties
% 2.45/1.03  
% 2.45/1.03  clauses:                                24
% 2.45/1.03  conjectures:                            1
% 2.45/1.03  epr:                                    1
% 2.45/1.03  horn:                                   16
% 2.45/1.03  ground:                                 1
% 2.45/1.03  unary:                                  4
% 2.45/1.03  binary:                                 2
% 2.45/1.03  lits:                                   74
% 2.45/1.03  lits_eq:                                6
% 2.45/1.03  fd_pure:                                0
% 2.45/1.03  fd_pseudo:                              0
% 2.45/1.03  fd_cond:                                0
% 2.45/1.03  fd_pseudo_cond:                         6
% 2.45/1.03  ac_symbols:                             0
% 2.45/1.03  
% 2.45/1.03  ------ Propositional Solver
% 2.45/1.03  
% 2.45/1.03  prop_solver_calls:                      27
% 2.45/1.03  prop_fast_solver_calls:                 1597
% 2.45/1.03  smt_solver_calls:                       0
% 2.45/1.03  smt_fast_solver_calls:                  0
% 2.45/1.03  prop_num_of_clauses:                    2007
% 2.45/1.03  prop_preprocess_simplified:             6081
% 2.45/1.03  prop_fo_subsumed:                       91
% 2.45/1.03  prop_solver_time:                       0.
% 2.45/1.03  smt_solver_time:                        0.
% 2.45/1.03  smt_fast_solver_time:                   0.
% 2.45/1.03  prop_fast_solver_time:                  0.
% 2.45/1.03  prop_unsat_core_time:                   0.
% 2.45/1.03  
% 2.45/1.03  ------ QBF
% 2.45/1.03  
% 2.45/1.03  qbf_q_res:                              0
% 2.45/1.03  qbf_num_tautologies:                    0
% 2.45/1.03  qbf_prep_cycles:                        0
% 2.45/1.03  
% 2.45/1.03  ------ BMC1
% 2.45/1.03  
% 2.45/1.03  bmc1_current_bound:                     -1
% 2.45/1.03  bmc1_last_solved_bound:                 -1
% 2.45/1.03  bmc1_unsat_core_size:                   -1
% 2.45/1.03  bmc1_unsat_core_parents_size:           -1
% 2.45/1.03  bmc1_merge_next_fun:                    0
% 2.45/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation
% 2.45/1.03  
% 2.45/1.03  inst_num_of_clauses:                    369
% 2.45/1.03  inst_num_in_passive:                    84
% 2.45/1.03  inst_num_in_active:                     273
% 2.45/1.03  inst_num_in_unprocessed:                11
% 2.45/1.03  inst_num_of_loops:                      301
% 2.45/1.03  inst_num_of_learning_restarts:          0
% 2.45/1.03  inst_num_moves_active_passive:          24
% 2.45/1.03  inst_lit_activity:                      0
% 2.45/1.03  inst_lit_activity_moves:                0
% 2.45/1.03  inst_num_tautologies:                   0
% 2.45/1.03  inst_num_prop_implied:                  0
% 2.45/1.03  inst_num_existing_simplified:           0
% 2.45/1.03  inst_num_eq_res_simplified:             0
% 2.45/1.03  inst_num_child_elim:                    0
% 2.45/1.03  inst_num_of_dismatching_blockings:      108
% 2.45/1.03  inst_num_of_non_proper_insts:           286
% 2.45/1.03  inst_num_of_duplicates:                 0
% 2.45/1.03  inst_inst_num_from_inst_to_res:         0
% 2.45/1.03  inst_dismatching_checking_time:         0.
% 2.45/1.03  
% 2.45/1.03  ------ Resolution
% 2.45/1.03  
% 2.45/1.03  res_num_of_clauses:                     0
% 2.45/1.03  res_num_in_passive:                     0
% 2.45/1.03  res_num_in_active:                      0
% 2.45/1.03  res_num_of_loops:                       125
% 2.45/1.03  res_forward_subset_subsumed:            11
% 2.45/1.03  res_backward_subset_subsumed:           0
% 2.45/1.03  res_forward_subsumed:                   0
% 2.45/1.03  res_backward_subsumed:                  0
% 2.45/1.03  res_forward_subsumption_resolution:     5
% 2.45/1.03  res_backward_subsumption_resolution:    1
% 2.45/1.03  res_clause_to_clause_subsumption:       305
% 2.45/1.03  res_orphan_elimination:                 0
% 2.45/1.03  res_tautology_del:                      19
% 2.45/1.03  res_num_eq_res_simplified:              0
% 2.45/1.03  res_num_sel_changes:                    0
% 2.45/1.03  res_moves_from_active_to_pass:          0
% 2.45/1.03  
% 2.45/1.03  ------ Superposition
% 2.45/1.03  
% 2.45/1.03  sup_time_total:                         0.
% 2.45/1.03  sup_time_generating:                    0.
% 2.45/1.03  sup_time_sim_full:                      0.
% 2.45/1.03  sup_time_sim_immed:                     0.
% 2.45/1.03  
% 2.45/1.03  sup_num_of_clauses:                     86
% 2.45/1.03  sup_num_in_active:                      60
% 2.45/1.03  sup_num_in_passive:                     26
% 2.45/1.03  sup_num_of_loops:                       60
% 2.45/1.03  sup_fw_superposition:                   31
% 2.45/1.03  sup_bw_superposition:                   36
% 2.45/1.03  sup_immediate_simplified:               2
% 2.45/1.03  sup_given_eliminated:                   0
% 2.45/1.03  comparisons_done:                       0
% 2.45/1.03  comparisons_avoided:                    0
% 2.45/1.03  
% 2.45/1.03  ------ Simplifications
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  sim_fw_subset_subsumed:                 2
% 2.45/1.03  sim_bw_subset_subsumed:                 0
% 2.45/1.03  sim_fw_subsumed:                        0
% 2.45/1.03  sim_bw_subsumed:                        0
% 2.45/1.03  sim_fw_subsumption_res:                 5
% 2.45/1.03  sim_bw_subsumption_res:                 0
% 2.45/1.03  sim_tautology_del:                      0
% 2.45/1.03  sim_eq_tautology_del:                   1
% 2.45/1.03  sim_eq_res_simp:                        0
% 2.45/1.03  sim_fw_demodulated:                     0
% 2.45/1.03  sim_bw_demodulated:                     0
% 2.45/1.03  sim_light_normalised:                   0
% 2.45/1.03  sim_joinable_taut:                      0
% 2.45/1.03  sim_joinable_simp:                      0
% 2.45/1.03  sim_ac_normalised:                      0
% 2.45/1.03  sim_smt_subsumption:                    0
% 2.45/1.03  
%------------------------------------------------------------------------------

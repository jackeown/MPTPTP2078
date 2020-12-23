%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:11 EST 2020

% Result     : Theorem 23.30s
% Output     : CNFRefutation 23.30s
% Verified   : 
% Statistics : Number of formulae       :  267 (1184 expanded)
%              Number of clauses        :  180 ( 282 expanded)
%              Number of leaves         :   22 ( 364 expanded)
%              Depth                    :   22
%              Number of atoms          : 1394 (7517 expanded)
%              Number of equality atoms :  109 ( 170 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
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
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
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
                ( r3_lattice3(X0,X1,X2)
               => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
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
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
          & r3_lattice3(X0,X1,X2) )
     => ( ~ r3_lattices(X0,X1,k16_lattice3(X0,sK9))
        & r3_lattice3(X0,X1,sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r3_lattices(X0,sK8,k16_lattice3(X0,X2))
            & r3_lattice3(X0,sK8,X2) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
                & r3_lattice3(X0,X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK7,X1,k16_lattice3(sK7,X2))
              & r3_lattice3(sK7,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK7)) )
      & l3_lattices(sK7)
      & v4_lattice3(sK7)
      & v10_lattices(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ r3_lattices(sK7,sK8,k16_lattice3(sK7,sK9))
    & r3_lattice3(sK7,sK8,sK9)
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l3_lattices(sK7)
    & v4_lattice3(sK7)
    & v10_lattices(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f55,f54,f53])).

fof(f86,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f48])).

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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
        & r3_lattice3(X0,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK6(X0,X1,X2),X2)
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f51])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | r3_lattice3(X0,sK6(X0,X1,X2),X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK5(X0,X1,X2),X2)
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK5(X0,X1,X2),X2)
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_9_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r4_lattice3(X0,X3,X1)
                 => r1_lattices(X0,X2,X3) ) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_lattices(X0,X5,X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,X5,X4)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_lattices(X0,X5,X6)
              | ~ r4_lattice3(X0,X6,X4)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r4_lattice3(X0,X5,X4)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_lattices(X0,sK4(X0,X4),X6)
            | ~ r4_lattice3(X0,X6,X4)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r4_lattice3(X0,sK4(X0,X4),X4)
        & m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK3(X0,X2))
        & r4_lattice3(X0,sK3(X0,X2),X1)
        & m1_subset_1(sK3(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,sK2(X0))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,sK2(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_lattices(X0,X2,sK3(X0,X2))
                & r4_lattice3(X0,sK3(X0,X2),sK2(X0))
                & m1_subset_1(sK3(X0,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,sK2(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_lattices(X0,sK4(X0,X4),X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,sK4(X0,X4),X4)
              & m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).

fof(f73,plain,(
    ! [X6,X4,X0] :
      ( r1_lattices(X0,sK4(X0,X4),X6)
      | ~ r4_lattice3(X0,X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK4(X0,X4),u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK5(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
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

fof(f58,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X4,X0] :
      ( r4_lattice3(X0,sK4(X0,X4),X4)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f92,plain,(
    ~ r3_lattices(sK7,sK8,k16_lattice3(sK7,sK9)) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    r3_lattice3(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1222,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_35])).

cnf(c_1223,plain,
    ( r3_lattice3(sK7,X0,X1)
    | r2_hidden(sK0(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1222])).

cnf(c_32,negated_conjecture,
    ( l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1227,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(sK0(sK7,X0,X1),X1)
    | r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1223,c_32])).

cnf(c_1228,plain,
    ( r3_lattice3(sK7,X0,X1)
    | r2_hidden(sK0(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1227])).

cnf(c_3040,plain,
    ( r3_lattice3(sK7,X0_55,X0_56)
    | r2_hidden(sK0(sK7,X0_55,X0_56),X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1228])).

cnf(c_4453,plain,
    ( r3_lattice3(sK7,sK4(sK7,X0_56),X1_56)
    | r2_hidden(sK0(sK7,sK4(sK7,X0_56),X1_56),X1_56)
    | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3040])).

cnf(c_62342,plain,
    ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
    | r2_hidden(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),X1_56)
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4453])).

cnf(c_62344,plain,
    ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
    | r2_hidden(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK9)
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_62342])).

cnf(c_3069,plain,
    ( ~ m1_subset_1(X0_55,X0_57)
    | m1_subset_1(X1_55,X0_57)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_3921,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(X1_55,u1_struct_0(sK7))
    | X1_55 != X0_55 ),
    inference(instantiation,[status(thm)],[c_3069])).

cnf(c_4096,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(k16_lattice3(sK7,X0_56),u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) != X0_55 ),
    inference(instantiation,[status(thm)],[c_3921])).

cnf(c_48967,plain,
    ( m1_subset_1(k16_lattice3(sK7,X0_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X1_56)),u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) != sK4(sK7,a_2_9_lattice3(sK7,X1_56)) ),
    inference(instantiation,[status(thm)],[c_4096])).

cnf(c_48969,plain,
    ( m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7))
    | k16_lattice3(sK7,sK9) != sK4(sK7,a_2_9_lattice3(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_48967])).

cnf(c_25,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_744,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k16_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_745,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_33,negated_conjecture,
    ( v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
    | ~ r3_lattice3(sK7,X0,X1)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_35,c_33,c_32])).

cnf(c_750,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k16_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_749])).

cnf(c_3055,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | r3_lattice3(sK7,sK6(sK7,X0_55,X0_56),X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_750])).

cnf(c_24398,plain,
    ( r3_lattice3(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X0_56),X0_56)
    | ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X0_56)
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) = sK4(sK7,a_2_9_lattice3(sK7,X0_56)) ),
    inference(instantiation,[status(thm)],[c_3055])).

cnf(c_24400,plain,
    ( r3_lattice3(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK9)
    | ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7))
    | k16_lattice3(sK7,sK9) = sK4(sK7,a_2_9_lattice3(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_24398])).

cnf(c_20,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_9_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_810,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_9_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_811,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r2_hidden(X0,a_2_9_lattice3(sK7,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(X0,a_2_9_lattice3(sK7,X1))
    | ~ r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_35,c_33,c_32])).

cnf(c_816,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r2_hidden(X0,a_2_9_lattice3(sK7,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_815])).

cnf(c_3052,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_816])).

cnf(c_8632,plain,
    ( ~ r3_lattice3(sK7,sK6(sK7,X0_55,X0_56),X1_56)
    | r2_hidden(sK6(sK7,X0_55,X0_56),a_2_9_lattice3(sK7,X1_56))
    | ~ m1_subset_1(sK6(sK7,X0_55,X0_56),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3052])).

cnf(c_15182,plain,
    ( ~ r3_lattice3(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),X0_56)
    | r2_hidden(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),a_2_9_lattice3(sK7,X0_56))
    | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_8632])).

cnf(c_15184,plain,
    ( ~ r3_lattice3(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK9)
    | r2_hidden(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),a_2_9_lattice3(sK7,sK9))
    | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_15182])).

cnf(c_6,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1243,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_35])).

cnf(c_1244,plain,
    ( r3_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1243])).

cnf(c_1248,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
    | r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1244,c_32])).

cnf(c_1249,plain,
    ( r3_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1248])).

cnf(c_3039,plain,
    ( r3_lattice3(sK7,X0_55,X0_56)
    | ~ r1_lattices(sK7,X0_55,sK0(sK7,X0_55,X0_56))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1249])).

cnf(c_17,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,sK4(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1057,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,sK4(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_1058,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,sK4(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1057])).

cnf(c_1062,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,sK4(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1058,c_33,c_32])).

cnf(c_3047,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_56)
    | r1_lattices(sK7,sK4(sK7,X0_56),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1062])).

cnf(c_4345,plain,
    ( ~ r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56)
    | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56)
    | ~ m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_3039,c_3047])).

cnf(c_3602,plain,
    ( r4_lattice3(sK7,X0_55,X0_56) != iProver_top
    | r1_lattices(sK7,sK4(sK7,X0_56),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3047])).

cnf(c_3610,plain,
    ( r3_lattice3(sK7,X0_55,X0_56) = iProver_top
    | r1_lattices(sK7,X0_55,sK0(sK7,X0_55,X0_56)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3039])).

cnf(c_4400,plain,
    ( r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56) != iProver_top
    | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) = iProver_top
    | m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3602,c_3610])).

cnf(c_19,plain,
    ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1027,plain,
    ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_1028,plain,
    ( m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1027])).

cnf(c_1032,plain,
    ( m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1028,c_33,c_32])).

cnf(c_3049,plain,
    ( m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1032])).

cnf(c_3117,plain,
    ( m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3049])).

cnf(c_4346,plain,
    ( r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56) != iProver_top
    | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) = iProver_top
    | m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4345])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1201,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_35])).

cnf(c_1202,plain,
    ( r3_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1201])).

cnf(c_1206,plain,
    ( m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1202,c_32])).

cnf(c_1207,plain,
    ( r3_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1206])).

cnf(c_3041,plain,
    ( r3_lattice3(sK7,X0_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X0_55,X0_56),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1207])).

cnf(c_4455,plain,
    ( r3_lattice3(sK7,sK4(sK7,X0_56),X1_56)
    | m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3041])).

cnf(c_4456,plain,
    ( r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) = iProver_top
    | m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4455])).

cnf(c_7183,plain,
    ( r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56) != iProver_top
    | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4400,c_3117,c_4346,c_4456])).

cnf(c_7185,plain,
    ( ~ r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56)
    | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7183])).

cnf(c_9636,plain,
    ( ~ r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56)
    | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4345,c_7185])).

cnf(c_3066,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_3065,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_4174,plain,
    ( X0_55 != X1_55
    | X1_55 = X0_55 ),
    inference(resolution,[status(thm)],[c_3066,c_3065])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK5(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_849,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK5(X0,X1,X2) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_850,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | sK5(X0,sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_849])).

cnf(c_854,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1))
    | sK5(X0,sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_850,c_35,c_33,c_32])).

cnf(c_3050,plain,
    ( ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56))
    | sK5(X0_55,sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_854])).

cnf(c_5052,plain,
    ( ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56))
    | X0_55 = sK5(X0_55,sK7,X0_56) ),
    inference(resolution,[status(thm)],[c_4174,c_3050])).

cnf(c_3070,plain,
    ( ~ r3_lattice3(X0_54,X0_55,X0_56)
    | r3_lattice3(X0_54,X1_55,X0_56)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_5227,plain,
    ( r3_lattice3(X0_54,X0_55,X0_56)
    | ~ r3_lattice3(X0_54,sK5(X0_55,sK7,X1_56),X0_56)
    | ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X1_56)) ),
    inference(resolution,[status(thm)],[c_5052,c_3070])).

cnf(c_21,plain,
    ( r3_lattice3(X0,sK5(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_9_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_792,plain,
    ( r3_lattice3(X0,sK5(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_9_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_793,plain,
    ( r3_lattice3(sK7,sK5(X0,sK7,X1),X1)
    | ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_797,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1))
    | r3_lattice3(sK7,sK5(X0,sK7,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_793,c_35,c_33,c_32])).

cnf(c_798,plain,
    ( r3_lattice3(sK7,sK5(X0,sK7,X1),X1)
    | ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1)) ),
    inference(renaming,[status(thm)],[c_797])).

cnf(c_3053,plain,
    ( r3_lattice3(sK7,sK5(X0_55,sK7,X0_56),X0_56)
    | ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56)) ),
    inference(subtyping,[status(esa)],[c_798])).

cnf(c_7559,plain,
    ( r3_lattice3(sK7,X0_55,X0_56)
    | ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56)) ),
    inference(resolution,[status(thm)],[c_5227,c_3053])).

cnf(c_11,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1132,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_1133,plain,
    ( r4_lattice3(sK7,X0,X1)
    | r2_hidden(sK1(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1132])).

cnf(c_1137,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(sK1(sK7,X0,X1),X1)
    | r4_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1133,c_32])).

cnf(c_1138,plain,
    ( r4_lattice3(sK7,X0,X1)
    | r2_hidden(sK1(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1137])).

cnf(c_3044,plain,
    ( r4_lattice3(sK7,X0_55,X0_56)
    | r2_hidden(sK1(sK7,X0_55,X0_56),X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1138])).

cnf(c_7708,plain,
    ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
    | r3_lattice3(sK7,sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_7559,c_3044])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1174,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_35])).

cnf(c_1175,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1174])).

cnf(c_1179,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1175,c_32])).

cnf(c_1180,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1179])).

cnf(c_3042,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | r1_lattices(sK7,X0_55,X1_55)
    | ~ r2_hidden(X1_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1180])).

cnf(c_7901,plain,
    ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
    | r1_lattices(sK7,sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),X1_55)
    | ~ r2_hidden(X1_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_7708,c_3042])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1111,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_1112,plain,
    ( r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1111])).

cnf(c_1116,plain,
    ( m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r4_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1112,c_32])).

cnf(c_1117,plain,
    ( r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1116])).

cnf(c_3045,plain,
    ( r4_lattice3(sK7,X0_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7,X0_55,X0_56),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1117])).

cnf(c_4349,plain,
    ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3045])).

cnf(c_14911,plain,
    ( ~ m1_subset_1(X1_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ r2_hidden(X1_55,X0_56)
    | r1_lattices(sK7,sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),X1_55)
    | r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7901,c_4349])).

cnf(c_14912,plain,
    ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
    | r1_lattices(sK7,sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),X1_55)
    | ~ r2_hidden(X1_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_14911])).

cnf(c_10,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1153,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_1154,plain,
    ( r4_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,sK1(sK7,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1153])).

cnf(c_1158,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,sK1(sK7,X0,X1),X0)
    | r4_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1154,c_32])).

cnf(c_1159,plain,
    ( r4_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,sK1(sK7,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1158])).

cnf(c_3043,plain,
    ( r4_lattice3(sK7,X0_55,X0_56)
    | ~ r1_lattices(sK7,sK1(sK7,X0_55,X0_56),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1159])).

cnf(c_15100,plain,
    ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
    | ~ r2_hidden(X0_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_14912,c_3043])).

cnf(c_15147,plain,
    ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
    | ~ r2_hidden(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),X0_56)
    | ~ m1_subset_1(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_9636,c_15100])).

cnf(c_15149,plain,
    ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
    | ~ r2_hidden(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK9)
    | ~ m1_subset_1(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_15147])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1084,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_1085,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1084])).

cnf(c_1089,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK7,X2,X0)
    | ~ r4_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1085,c_32])).

cnf(c_1090,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1089])).

cnf(c_3046,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_56)
    | r1_lattices(sK7,X1_55,X0_55)
    | ~ r2_hidden(X1_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1090])).

cnf(c_3871,plain,
    ( ~ r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
    | r1_lattices(sK7,X1_55,X0_55)
    | ~ r2_hidden(X1_55,a_2_9_lattice3(sK7,X0_56))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_4004,plain,
    ( ~ r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),a_2_9_lattice3(sK7,X0_56))
    | r1_lattices(sK7,X0_55,sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
    | ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3871])).

cnf(c_9899,plain,
    ( ~ r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),a_2_9_lattice3(sK7,X0_56))
    | r1_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
    | ~ r2_hidden(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),a_2_9_lattice3(sK7,X0_56))
    | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4004])).

cnf(c_9901,plain,
    ( ~ r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),a_2_9_lattice3(sK7,sK9))
    | r1_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK4(sK7,a_2_9_lattice3(sK7,sK9)))
    | ~ r2_hidden(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),a_2_9_lattice3(sK7,sK9))
    | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9899])).

cnf(c_6843,plain,
    ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
    | m1_subset_1(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4455])).

cnf(c_6845,plain,
    ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
    | m1_subset_1(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_6843])).

cnf(c_26,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_720,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k16_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_721,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_725,plain,
    ( m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r3_lattice3(sK7,X0,X1)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_35,c_33,c_32])).

cnf(c_726,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
    | k16_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_725])).

cnf(c_3056,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0_55,X0_56),u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_726])).

cnf(c_6410,plain,
    ( ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
    | m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7))
    | k16_lattice3(sK7,X1_56) = sK4(sK7,a_2_9_lattice3(sK7,X0_56)) ),
    inference(instantiation,[status(thm)],[c_3056])).

cnf(c_6412,plain,
    ( ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
    | m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7))
    | k16_lattice3(sK7,sK9) = sK4(sK7,a_2_9_lattice3(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_6410])).

cnf(c_24,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_768,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k16_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_769,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_768])).

cnf(c_773,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ r3_lattice3(sK7,X0,X1)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_769,c_35,c_33,c_32])).

cnf(c_774,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k16_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_773])).

cnf(c_3054,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | ~ r3_lattices(sK7,sK6(sK7,X0_55,X0_56),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_774])).

cnf(c_4988,plain,
    ( ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
    | ~ r3_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7))
    | k16_lattice3(sK7,X1_56) = sK4(sK7,a_2_9_lattice3(sK7,X0_56)) ),
    inference(instantiation,[status(thm)],[c_3054])).

cnf(c_4994,plain,
    ( ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
    | ~ r3_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK4(sK7,a_2_9_lattice3(sK7,sK9)))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7))
    | k16_lattice3(sK7,sK9) = sK4(sK7,a_2_9_lattice3(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_4988])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

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
    inference(cnf_transformation,[],[f62])).

cnf(c_416,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_420,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_2,c_1])).

cnf(c_630,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_420,c_34])).

cnf(c_631,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_635,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_631,c_35,c_32])).

cnf(c_636,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_635])).

cnf(c_3060,plain,
    ( ~ r1_lattices(sK7,X0_55,X1_55)
    | r3_lattices(sK7,X0_55,X1_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_636])).

cnf(c_4576,plain,
    ( ~ r1_lattices(sK7,X0_55,sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
    | r3_lattices(sK7,X0_55,sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3060])).

cnf(c_4987,plain,
    ( ~ r1_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
    | r3_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
    | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4576])).

cnf(c_4990,plain,
    ( ~ r1_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK4(sK7,a_2_9_lattice3(sK7,sK9)))
    | r3_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK4(sK7,a_2_9_lattice3(sK7,sK9)))
    | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4987])).

cnf(c_4244,plain,
    ( m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3049])).

cnf(c_4246,plain,
    ( m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4244])).

cnf(c_18,plain,
    ( r4_lattice3(X0,sK4(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1042,plain,
    ( r4_lattice3(X0,sK4(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_1043,plain,
    ( r4_lattice3(sK7,sK4(sK7,X0),X0)
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1042])).

cnf(c_1047,plain,
    ( r4_lattice3(sK7,sK4(sK7,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1043,c_33,c_32])).

cnf(c_3048,plain,
    ( r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) ),
    inference(subtyping,[status(esa)],[c_1047])).

cnf(c_4005,plain,
    ( r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),a_2_9_lattice3(sK7,X0_56)) ),
    inference(instantiation,[status(thm)],[c_3048])).

cnf(c_4011,plain,
    ( r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),a_2_9_lattice3(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_4005])).

cnf(c_27,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_696,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_697,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r3_lattices(sK7,X0,k16_lattice3(sK7,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k16_lattice3(sK7,X1),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_701,plain,
    ( ~ m1_subset_1(k16_lattice3(sK7,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r3_lattices(sK7,X0,k16_lattice3(sK7,X1))
    | ~ r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_697,c_35,c_33,c_32])).

cnf(c_702,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r3_lattices(sK7,X0,k16_lattice3(sK7,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k16_lattice3(sK7,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_701])).

cnf(c_3057,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | r3_lattices(sK7,X0_55,k16_lattice3(sK7,X0_56))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(k16_lattice3(sK7,X0_56),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_702])).

cnf(c_3094,plain,
    ( ~ r3_lattice3(sK7,sK8,sK9)
    | r3_lattices(sK7,sK8,k16_lattice3(sK7,sK9))
    | ~ m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3057])).

cnf(c_29,negated_conjecture,
    ( ~ r3_lattices(sK7,sK8,k16_lattice3(sK7,sK9)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_30,negated_conjecture,
    ( r3_lattice3(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f90])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62344,c_48969,c_24400,c_15184,c_15149,c_9901,c_6845,c_6412,c_4994,c_4990,c_4246,c_4011,c_3094,c_29,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:37:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.30/3.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.30/3.51  
% 23.30/3.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.30/3.51  
% 23.30/3.51  ------  iProver source info
% 23.30/3.51  
% 23.30/3.51  git: date: 2020-06-30 10:37:57 +0100
% 23.30/3.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.30/3.51  git: non_committed_changes: false
% 23.30/3.51  git: last_make_outside_of_git: false
% 23.30/3.51  
% 23.30/3.51  ------ 
% 23.30/3.51  ------ Parsing...
% 23.30/3.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.30/3.51  
% 23.30/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 23.30/3.51  
% 23.30/3.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.30/3.51  
% 23.30/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.30/3.51  ------ Proving...
% 23.30/3.51  ------ Problem Properties 
% 23.30/3.51  
% 23.30/3.51  
% 23.30/3.51  clauses                                 25
% 23.30/3.51  conjectures                             3
% 23.30/3.51  EPR                                     1
% 23.30/3.51  Horn                                    19
% 23.30/3.51  unary                                   5
% 23.30/3.51  binary                                  4
% 23.30/3.51  lits                                    71
% 23.30/3.51  lits eq                                 4
% 23.30/3.51  fd_pure                                 0
% 23.30/3.51  fd_pseudo                               0
% 23.30/3.51  fd_cond                                 0
% 23.30/3.51  fd_pseudo_cond                          3
% 23.30/3.51  AC symbols                              0
% 23.30/3.51  
% 23.30/3.51  ------ Input Options Time Limit: Unbounded
% 23.30/3.51  
% 23.30/3.51  
% 23.30/3.51  ------ 
% 23.30/3.51  Current options:
% 23.30/3.51  ------ 
% 23.30/3.51  
% 23.30/3.51  
% 23.30/3.51  
% 23.30/3.51  
% 23.30/3.51  ------ Proving...
% 23.30/3.51  
% 23.30/3.51  
% 23.30/3.51  % SZS status Theorem for theBenchmark.p
% 23.30/3.51  
% 23.30/3.51  % SZS output start CNFRefutation for theBenchmark.p
% 23.30/3.51  
% 23.30/3.51  fof(f3,axiom,(
% 23.30/3.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 23.30/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.30/3.51  
% 23.30/3.51  fof(f17,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.30/3.51    inference(ennf_transformation,[],[f3])).
% 23.30/3.51  
% 23.30/3.51  fof(f18,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(flattening,[],[f17])).
% 23.30/3.51  
% 23.30/3.51  fof(f30,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(nnf_transformation,[],[f18])).
% 23.30/3.51  
% 23.30/3.51  fof(f31,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(rectify,[],[f30])).
% 23.30/3.51  
% 23.30/3.51  fof(f32,plain,(
% 23.30/3.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f33,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 23.30/3.51  
% 23.30/3.51  fof(f65,plain,(
% 23.30/3.51    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f33])).
% 23.30/3.51  
% 23.30/3.51  fof(f8,conjecture,(
% 23.30/3.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 23.30/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.30/3.51  
% 23.30/3.51  fof(f9,negated_conjecture,(
% 23.30/3.51    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 23.30/3.51    inference(negated_conjecture,[],[f8])).
% 23.30/3.51  
% 23.30/3.51  fof(f27,plain,(
% 23.30/3.51    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 23.30/3.51    inference(ennf_transformation,[],[f9])).
% 23.30/3.51  
% 23.30/3.51  fof(f28,plain,(
% 23.30/3.51    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 23.30/3.51    inference(flattening,[],[f27])).
% 23.30/3.51  
% 23.30/3.51  fof(f55,plain,(
% 23.30/3.51    ( ! [X0,X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) => (~r3_lattices(X0,X1,k16_lattice3(X0,sK9)) & r3_lattice3(X0,X1,sK9))) )),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f54,plain,(
% 23.30/3.51    ( ! [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (~r3_lattices(X0,sK8,k16_lattice3(X0,X2)) & r3_lattice3(X0,sK8,X2)) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f53,plain,(
% 23.30/3.51    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK7,X1,k16_lattice3(sK7,X2)) & r3_lattice3(sK7,X1,X2)) & m1_subset_1(X1,u1_struct_0(sK7))) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7))),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f56,plain,(
% 23.30/3.51    ((~r3_lattices(sK7,sK8,k16_lattice3(sK7,sK9)) & r3_lattice3(sK7,sK8,sK9)) & m1_subset_1(sK8,u1_struct_0(sK7))) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7)),
% 23.30/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f55,f54,f53])).
% 23.30/3.51  
% 23.30/3.51  fof(f86,plain,(
% 23.30/3.51    ~v2_struct_0(sK7)),
% 23.30/3.51    inference(cnf_transformation,[],[f56])).
% 23.30/3.51  
% 23.30/3.51  fof(f89,plain,(
% 23.30/3.51    l3_lattices(sK7)),
% 23.30/3.51    inference(cnf_transformation,[],[f56])).
% 23.30/3.51  
% 23.30/3.51  fof(f7,axiom,(
% 23.30/3.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 23.30/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.30/3.51  
% 23.30/3.51  fof(f25,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.30/3.51    inference(ennf_transformation,[],[f7])).
% 23.30/3.51  
% 23.30/3.51  fof(f26,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(flattening,[],[f25])).
% 23.30/3.51  
% 23.30/3.51  fof(f48,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(nnf_transformation,[],[f26])).
% 23.30/3.51  
% 23.30/3.51  fof(f49,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(flattening,[],[f48])).
% 23.30/3.51  
% 23.30/3.51  fof(f50,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(rectify,[],[f49])).
% 23.30/3.51  
% 23.30/3.51  fof(f51,plain,(
% 23.30/3.51    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f52,plain,(
% 23.30/3.51    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f51])).
% 23.30/3.51  
% 23.30/3.51  fof(f84,plain,(
% 23.30/3.51    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | r3_lattice3(X0,sK6(X0,X1,X2),X2) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f52])).
% 23.30/3.51  
% 23.30/3.51  fof(f87,plain,(
% 23.30/3.51    v10_lattices(sK7)),
% 23.30/3.51    inference(cnf_transformation,[],[f56])).
% 23.30/3.51  
% 23.30/3.51  fof(f88,plain,(
% 23.30/3.51    v4_lattice3(sK7)),
% 23.30/3.51    inference(cnf_transformation,[],[f56])).
% 23.30/3.51  
% 23.30/3.51  fof(f6,axiom,(
% 23.30/3.51    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 23.30/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.30/3.51  
% 23.30/3.51  fof(f23,plain,(
% 23.30/3.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 23.30/3.51    inference(ennf_transformation,[],[f6])).
% 23.30/3.51  
% 23.30/3.51  fof(f24,plain,(
% 23.30/3.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.30/3.51    inference(flattening,[],[f23])).
% 23.30/3.51  
% 23.30/3.51  fof(f44,plain,(
% 23.30/3.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.30/3.51    inference(nnf_transformation,[],[f24])).
% 23.30/3.51  
% 23.30/3.51  fof(f45,plain,(
% 23.30/3.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.30/3.51    inference(rectify,[],[f44])).
% 23.30/3.51  
% 23.30/3.51  fof(f46,plain,(
% 23.30/3.51    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK5(X0,X1,X2),X2) & sK5(X0,X1,X2) = X0 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f47,plain,(
% 23.30/3.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK5(X0,X1,X2),X2) & sK5(X0,X1,X2) = X0 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.30/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 23.30/3.51  
% 23.30/3.51  fof(f80,plain,(
% 23.30/3.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f47])).
% 23.30/3.51  
% 23.30/3.51  fof(f93,plain,(
% 23.30/3.51    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_9_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 23.30/3.51    inference(equality_resolution,[],[f80])).
% 23.30/3.51  
% 23.30/3.51  fof(f66,plain,(
% 23.30/3.51    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f33])).
% 23.30/3.51  
% 23.30/3.51  fof(f5,axiom,(
% 23.30/3.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 23.30/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.30/3.51  
% 23.30/3.51  fof(f21,plain,(
% 23.30/3.51    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.30/3.51    inference(ennf_transformation,[],[f5])).
% 23.30/3.51  
% 23.30/3.51  fof(f22,plain,(
% 23.30/3.51    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(flattening,[],[f21])).
% 23.30/3.51  
% 23.30/3.51  fof(f38,plain,(
% 23.30/3.51    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(nnf_transformation,[],[f22])).
% 23.30/3.51  
% 23.30/3.51  fof(f39,plain,(
% 23.30/3.51    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : ? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(rectify,[],[f38])).
% 23.30/3.51  
% 23.30/3.51  fof(f42,plain,(
% 23.30/3.51    ! [X4,X0] : (? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r1_lattices(X0,sK4(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK4(X0,X4),X4) & m1_subset_1(sK4(X0,X4),u1_struct_0(X0))))),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f41,plain,(
% 23.30/3.51    ( ! [X1] : (! [X2,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK3(X0,X2)) & r4_lattice3(X0,sK3(X0,X2),X1) & m1_subset_1(sK3(X0,X2),u1_struct_0(X0))))) )),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f40,plain,(
% 23.30/3.51    ! [X0] : (? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK2(X0)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 23.30/3.51    introduced(choice_axiom,[])).
% 23.30/3.51  
% 23.30/3.51  fof(f43,plain,(
% 23.30/3.51    ! [X0] : (((v4_lattice3(X0) | ! [X2] : ((~r1_lattices(X0,X2,sK3(X0,X2)) & r4_lattice3(X0,sK3(X0,X2),sK2(X0)) & m1_subset_1(sK3(X0,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X6] : (r1_lattices(X0,sK4(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK4(X0,X4),X4) & m1_subset_1(sK4(X0,X4),u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).
% 23.30/3.51  
% 23.30/3.51  fof(f73,plain,(
% 23.30/3.51    ( ! [X6,X4,X0] : (r1_lattices(X0,sK4(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f43])).
% 23.30/3.51  
% 23.30/3.51  fof(f71,plain,(
% 23.30/3.51    ( ! [X4,X0] : (m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f43])).
% 23.30/3.51  
% 23.30/3.51  fof(f64,plain,(
% 23.30/3.51    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f33])).
% 23.30/3.51  
% 23.30/3.51  fof(f78,plain,(
% 23.30/3.51    ( ! [X2,X0,X1] : (sK5(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f47])).
% 23.30/3.51  
% 23.30/3.51  fof(f79,plain,(
% 23.30/3.51    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK5(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 23.30/3.51    inference(cnf_transformation,[],[f47])).
% 23.30/3.51  
% 23.30/3.51  fof(f4,axiom,(
% 23.30/3.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 23.30/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.30/3.52  
% 23.30/3.52  fof(f19,plain,(
% 23.30/3.52    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.30/3.52    inference(ennf_transformation,[],[f4])).
% 23.30/3.52  
% 23.30/3.52  fof(f20,plain,(
% 23.30/3.52    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.52    inference(flattening,[],[f19])).
% 23.30/3.52  
% 23.30/3.52  fof(f34,plain,(
% 23.30/3.52    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.52    inference(nnf_transformation,[],[f20])).
% 23.30/3.52  
% 23.30/3.52  fof(f35,plain,(
% 23.30/3.52    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.52    inference(rectify,[],[f34])).
% 23.30/3.52  
% 23.30/3.52  fof(f36,plain,(
% 23.30/3.52    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 23.30/3.52    introduced(choice_axiom,[])).
% 23.30/3.52  
% 23.30/3.52  fof(f37,plain,(
% 23.30/3.52    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 23.30/3.52  
% 23.30/3.52  fof(f69,plain,(
% 23.30/3.52    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f37])).
% 23.30/3.52  
% 23.30/3.52  fof(f63,plain,(
% 23.30/3.52    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f33])).
% 23.30/3.52  
% 23.30/3.52  fof(f68,plain,(
% 23.30/3.52    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f37])).
% 23.30/3.52  
% 23.30/3.52  fof(f70,plain,(
% 23.30/3.52    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f37])).
% 23.30/3.52  
% 23.30/3.52  fof(f67,plain,(
% 23.30/3.52    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f37])).
% 23.30/3.52  
% 23.30/3.52  fof(f83,plain,(
% 23.30/3.52    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f52])).
% 23.30/3.52  
% 23.30/3.52  fof(f85,plain,(
% 23.30/3.52    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | ~r3_lattices(X0,sK6(X0,X1,X2),X1) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f52])).
% 23.30/3.52  
% 23.30/3.52  fof(f1,axiom,(
% 23.30/3.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 23.30/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.30/3.52  
% 23.30/3.52  fof(f10,plain,(
% 23.30/3.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 23.30/3.52    inference(pure_predicate_removal,[],[f1])).
% 23.30/3.52  
% 23.30/3.52  fof(f11,plain,(
% 23.30/3.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 23.30/3.52    inference(pure_predicate_removal,[],[f10])).
% 23.30/3.52  
% 23.30/3.52  fof(f12,plain,(
% 23.30/3.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 23.30/3.52    inference(pure_predicate_removal,[],[f11])).
% 23.30/3.52  
% 23.30/3.52  fof(f13,plain,(
% 23.30/3.52    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 23.30/3.52    inference(ennf_transformation,[],[f12])).
% 23.30/3.52  
% 23.30/3.52  fof(f14,plain,(
% 23.30/3.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 23.30/3.52    inference(flattening,[],[f13])).
% 23.30/3.52  
% 23.30/3.52  fof(f60,plain,(
% 23.30/3.52    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f14])).
% 23.30/3.52  
% 23.30/3.52  fof(f2,axiom,(
% 23.30/3.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 23.30/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.30/3.52  
% 23.30/3.52  fof(f15,plain,(
% 23.30/3.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 23.30/3.52    inference(ennf_transformation,[],[f2])).
% 23.30/3.52  
% 23.30/3.52  fof(f16,plain,(
% 23.30/3.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.52    inference(flattening,[],[f15])).
% 23.30/3.52  
% 23.30/3.52  fof(f29,plain,(
% 23.30/3.52    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.30/3.52    inference(nnf_transformation,[],[f16])).
% 23.30/3.52  
% 23.30/3.52  fof(f62,plain,(
% 23.30/3.52    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f29])).
% 23.30/3.52  
% 23.30/3.52  fof(f58,plain,(
% 23.30/3.52    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f14])).
% 23.30/3.52  
% 23.30/3.52  fof(f59,plain,(
% 23.30/3.52    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f14])).
% 23.30/3.52  
% 23.30/3.52  fof(f72,plain,(
% 23.30/3.52    ( ! [X4,X0] : (r4_lattice3(X0,sK4(X0,X4),X4) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f43])).
% 23.30/3.52  
% 23.30/3.52  fof(f82,plain,(
% 23.30/3.52    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(cnf_transformation,[],[f52])).
% 23.30/3.52  
% 23.30/3.52  fof(f94,plain,(
% 23.30/3.52    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.30/3.52    inference(equality_resolution,[],[f82])).
% 23.30/3.52  
% 23.30/3.52  fof(f92,plain,(
% 23.30/3.52    ~r3_lattices(sK7,sK8,k16_lattice3(sK7,sK9))),
% 23.30/3.52    inference(cnf_transformation,[],[f56])).
% 23.30/3.52  
% 23.30/3.52  fof(f91,plain,(
% 23.30/3.52    r3_lattice3(sK7,sK8,sK9)),
% 23.30/3.52    inference(cnf_transformation,[],[f56])).
% 23.30/3.52  
% 23.30/3.52  fof(f90,plain,(
% 23.30/3.52    m1_subset_1(sK8,u1_struct_0(sK7))),
% 23.30/3.52    inference(cnf_transformation,[],[f56])).
% 23.30/3.52  
% 23.30/3.52  cnf(c_7,plain,
% 23.30/3.52      ( r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f65]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_35,negated_conjecture,
% 23.30/3.52      ( ~ v2_struct_0(sK7) ),
% 23.30/3.52      inference(cnf_transformation,[],[f86]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1222,plain,
% 23.30/3.52      ( r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_7,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1223,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r2_hidden(sK0(sK7,X0,X1),X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1222]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_32,negated_conjecture,
% 23.30/3.52      ( l3_lattices(sK7) ),
% 23.30/3.52      inference(cnf_transformation,[],[f89]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1227,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | r2_hidden(sK0(sK7,X0,X1),X1)
% 23.30/3.52      | r3_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1223,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1228,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r2_hidden(sK0(sK7,X0,X1),X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_1227]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3040,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | r2_hidden(sK0(sK7,X0_55,X0_56),X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1228]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4453,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,X0_56),X1_56)
% 23.30/3.52      | r2_hidden(sK0(sK7,sK4(sK7,X0_56),X1_56),X1_56)
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3040]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_62342,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
% 23.30/3.52      | r2_hidden(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),X1_56)
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4453]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_62344,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
% 23.30/3.52      | r2_hidden(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK9)
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_62342]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3069,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0_55,X0_57)
% 23.30/3.52      | m1_subset_1(X1_55,X0_57)
% 23.30/3.52      | X1_55 != X0_55 ),
% 23.30/3.52      theory(equality) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3921,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(X1_55,u1_struct_0(sK7))
% 23.30/3.52      | X1_55 != X0_55 ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3069]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4096,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(k16_lattice3(sK7,X0_56),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X0_56) != X0_55 ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3921]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_48967,plain,
% 23.30/3.52      ( m1_subset_1(k16_lattice3(sK7,X0_56),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X1_56)),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X0_56) != sK4(sK7,a_2_9_lattice3(sK7,X1_56)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4096]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_48969,plain,
% 23.30/3.52      ( m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,sK9) != sK4(sK7,a_2_9_lattice3(sK7,sK9)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_48967]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_25,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r3_lattice3(X0,sK6(X0,X1,X2),X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0)
% 23.30/3.52      | k16_lattice3(X0,X2) = X1 ),
% 23.30/3.52      inference(cnf_transformation,[],[f84]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_34,negated_conjecture,
% 23.30/3.52      ( v10_lattices(sK7) ),
% 23.30/3.52      inference(cnf_transformation,[],[f87]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_744,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r3_lattice3(X0,sK6(X0,X1,X2),X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | k16_lattice3(X0,X2) = X1
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_745,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7)
% 23.30/3.52      | v2_struct_0(sK7)
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_744]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_33,negated_conjecture,
% 23.30/3.52      ( v4_lattice3(sK7) ),
% 23.30/3.52      inference(cnf_transformation,[],[f88]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_749,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
% 23.30/3.52      | ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_745,c_35,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_750,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_749]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3055,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | r3_lattice3(sK7,sK6(sK7,X0_55,X0_56),X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X0_56) = X0_55 ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_750]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_24398,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X0_56),X0_56)
% 23.30/3.52      | ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X0_56)
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X0_56) = sK4(sK7,a_2_9_lattice3(sK7,X0_56)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3055]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_24400,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK9)
% 23.30/3.52      | ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,sK9) = sK4(sK7,a_2_9_lattice3(sK7,sK9)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_24398]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_20,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r2_hidden(X1,a_2_9_lattice3(X0,X2))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f93]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_810,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r2_hidden(X1,a_2_9_lattice3(X0,X2))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_811,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r2_hidden(X0,a_2_9_lattice3(sK7,X1))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7)
% 23.30/3.52      | v2_struct_0(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_810]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_815,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | r2_hidden(X0,a_2_9_lattice3(sK7,X1))
% 23.30/3.52      | ~ r3_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_811,c_35,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_816,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r2_hidden(X0,a_2_9_lattice3(sK7,X1))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_815]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3052,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_816]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_8632,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,sK6(sK7,X0_55,X0_56),X1_56)
% 23.30/3.52      | r2_hidden(sK6(sK7,X0_55,X0_56),a_2_9_lattice3(sK7,X1_56))
% 23.30/3.52      | ~ m1_subset_1(sK6(sK7,X0_55,X0_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3052]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_15182,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),X0_56)
% 23.30/3.52      | r2_hidden(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_8632]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_15184,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK9)
% 23.30/3.52      | r2_hidden(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),a_2_9_lattice3(sK7,sK9))
% 23.30/3.52      | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_15182]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_6,plain,
% 23.30/3.52      ( r3_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f66]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1243,plain,
% 23.30/3.52      ( r3_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_6,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1244,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1243]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1248,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
% 23.30/3.52      | r3_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1244,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1249,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_1248]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3039,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | ~ r1_lattices(sK7,X0_55,sK0(sK7,X0_55,X0_56))
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1249]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_17,plain,
% 23.30/3.52      ( ~ r4_lattice3(X0,X1,X2)
% 23.30/3.52      | r1_lattices(X0,sK4(X0,X2),X1)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f73]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1057,plain,
% 23.30/3.52      ( ~ r4_lattice3(X0,X1,X2)
% 23.30/3.52      | r1_lattices(X0,sK4(X0,X2),X1)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1058,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | r1_lattices(sK7,sK4(sK7,X1),X0)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1057]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1062,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | r1_lattices(sK7,sK4(sK7,X1),X0)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1058,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3047,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | r1_lattices(sK7,sK4(sK7,X0_56),X0_55)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1062]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4345,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56)
% 23.30/3.52      | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56)
% 23.30/3.52      | ~ m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_3039,c_3047]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3602,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,X0_56) != iProver_top
% 23.30/3.52      | r1_lattices(sK7,sK4(sK7,X0_56),X0_55) = iProver_top
% 23.30/3.52      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 23.30/3.52      inference(predicate_to_equality,[status(thm)],[c_3047]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3610,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0_55,X0_56) = iProver_top
% 23.30/3.52      | r1_lattices(sK7,X0_55,sK0(sK7,X0_55,X0_56)) != iProver_top
% 23.30/3.52      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 23.30/3.52      inference(predicate_to_equality,[status(thm)],[c_3039]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4400,plain,
% 23.30/3.52      ( r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56) != iProver_top
% 23.30/3.52      | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) = iProver_top
% 23.30/3.52      | m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7)) != iProver_top
% 23.30/3.52      | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
% 23.30/3.52      inference(superposition,[status(thm)],[c_3602,c_3610]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_19,plain,
% 23.30/3.52      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f71]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1027,plain,
% 23.30/3.52      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1028,plain,
% 23.30/3.52      ( m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1027]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1032,plain,
% 23.30/3.52      ( m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1028,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3049,plain,
% 23.30/3.52      ( m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1032]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3117,plain,
% 23.30/3.52      ( m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) = iProver_top ),
% 23.30/3.52      inference(predicate_to_equality,[status(thm)],[c_3049]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4346,plain,
% 23.30/3.52      ( r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56) != iProver_top
% 23.30/3.52      | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) = iProver_top
% 23.30/3.52      | m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7)) != iProver_top
% 23.30/3.52      | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
% 23.30/3.52      inference(predicate_to_equality,[status(thm)],[c_4345]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_8,plain,
% 23.30/3.52      ( r3_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f64]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1201,plain,
% 23.30/3.52      ( r3_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_8,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1202,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1201]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1206,plain,
% 23.30/3.52      ( m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | r3_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1202,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1207,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_1206]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3041,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK0(sK7,X0_55,X0_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1207]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4455,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,X0_56),X1_56)
% 23.30/3.52      | m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3041]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4456,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) = iProver_top
% 23.30/3.52      | m1_subset_1(sK0(sK7,sK4(sK7,X0_56),X1_56),u1_struct_0(sK7)) = iProver_top
% 23.30/3.52      | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
% 23.30/3.52      inference(predicate_to_equality,[status(thm)],[c_4455]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_7183,plain,
% 23.30/3.52      ( r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56) != iProver_top
% 23.30/3.52      | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) = iProver_top ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_4400,c_3117,c_4346,c_4456]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_7185,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56)
% 23.30/3.52      | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) ),
% 23.30/3.52      inference(predicate_to_equality_rev,[status(thm)],[c_7183]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_9636,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,sK0(sK7,sK4(sK7,X0_56),X1_56),X0_56)
% 23.30/3.52      | r3_lattice3(sK7,sK4(sK7,X0_56),X1_56) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_4345,c_7185]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3066,plain,
% 23.30/3.52      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 23.30/3.52      theory(equality) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3065,plain,( X0_55 = X0_55 ),theory(equality) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4174,plain,
% 23.30/3.52      ( X0_55 != X1_55 | X1_55 = X0_55 ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_3066,c_3065]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_22,plain,
% 23.30/3.52      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
% 23.30/3.52      | ~ v4_lattice3(X1)
% 23.30/3.52      | ~ l3_lattices(X1)
% 23.30/3.52      | v2_struct_0(X1)
% 23.30/3.52      | ~ v10_lattices(X1)
% 23.30/3.52      | sK5(X0,X1,X2) = X0 ),
% 23.30/3.52      inference(cnf_transformation,[],[f78]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_849,plain,
% 23.30/3.52      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
% 23.30/3.52      | ~ v4_lattice3(X1)
% 23.30/3.52      | ~ l3_lattices(X1)
% 23.30/3.52      | v2_struct_0(X1)
% 23.30/3.52      | sK5(X0,X1,X2) = X0
% 23.30/3.52      | sK7 != X1 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_850,plain,
% 23.30/3.52      ( ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7)
% 23.30/3.52      | v2_struct_0(sK7)
% 23.30/3.52      | sK5(X0,sK7,X1) = X0 ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_849]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_854,plain,
% 23.30/3.52      ( ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1)) | sK5(X0,sK7,X1) = X0 ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_850,c_35,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3050,plain,
% 23.30/3.52      ( ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | sK5(X0_55,sK7,X0_56) = X0_55 ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_854]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_5052,plain,
% 23.30/3.52      ( ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | X0_55 = sK5(X0_55,sK7,X0_56) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_4174,c_3050]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3070,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0_54,X0_55,X0_56)
% 23.30/3.52      | r3_lattice3(X0_54,X1_55,X0_56)
% 23.30/3.52      | X1_55 != X0_55 ),
% 23.30/3.52      theory(equality) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_5227,plain,
% 23.30/3.52      ( r3_lattice3(X0_54,X0_55,X0_56)
% 23.30/3.52      | ~ r3_lattice3(X0_54,sK5(X0_55,sK7,X1_56),X0_56)
% 23.30/3.52      | ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X1_56)) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_5052,c_3070]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_21,plain,
% 23.30/3.52      ( r3_lattice3(X0,sK5(X1,X0,X2),X2)
% 23.30/3.52      | ~ r2_hidden(X1,a_2_9_lattice3(X0,X2))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f79]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_792,plain,
% 23.30/3.52      ( r3_lattice3(X0,sK5(X1,X0,X2),X2)
% 23.30/3.52      | ~ r2_hidden(X1,a_2_9_lattice3(X0,X2))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_793,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK5(X0,sK7,X1),X1)
% 23.30/3.52      | ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7)
% 23.30/3.52      | v2_struct_0(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_792]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_797,plain,
% 23.30/3.52      ( ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1))
% 23.30/3.52      | r3_lattice3(sK7,sK5(X0,sK7,X1),X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_793,c_35,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_798,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK5(X0,sK7,X1),X1)
% 23.30/3.52      | ~ r2_hidden(X0,a_2_9_lattice3(sK7,X1)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_797]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3053,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK5(X0_55,sK7,X0_56),X0_56)
% 23.30/3.52      | ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_798]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_7559,plain,
% 23.30/3.52      ( r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56)) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_5227,c_3053]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_11,plain,
% 23.30/3.52      ( r4_lattice3(X0,X1,X2)
% 23.30/3.52      | r2_hidden(sK1(X0,X1,X2),X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f69]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1132,plain,
% 23.30/3.52      ( r4_lattice3(X0,X1,X2)
% 23.30/3.52      | r2_hidden(sK1(X0,X1,X2),X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1133,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | r2_hidden(sK1(sK7,X0,X1),X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1132]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1137,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | r2_hidden(sK1(sK7,X0,X1),X1)
% 23.30/3.52      | r4_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1133,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1138,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | r2_hidden(sK1(sK7,X0,X1),X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_1137]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3044,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | r2_hidden(sK1(sK7,X0_55,X0_56),X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1138]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_7708,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | r3_lattice3(sK7,sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_7559,c_3044]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_9,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r1_lattices(X0,X1,X3)
% 23.30/3.52      | ~ r2_hidden(X3,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f63]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1174,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r1_lattices(X0,X1,X3)
% 23.30/3.52      | ~ r2_hidden(X3,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_9,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1175,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r1_lattices(sK7,X0,X2)
% 23.30/3.52      | ~ r2_hidden(X2,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1174]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1179,plain,
% 23.30/3.52      ( ~ m1_subset_1(X2,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ r2_hidden(X2,X1)
% 23.30/3.52      | r1_lattices(sK7,X0,X2)
% 23.30/3.52      | ~ r3_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1175,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1180,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r1_lattices(sK7,X0,X2)
% 23.30/3.52      | ~ r2_hidden(X2,X1)
% 23.30/3.52      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_1179]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3042,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | r1_lattices(sK7,X0_55,X1_55)
% 23.30/3.52      | ~ r2_hidden(X1_55,X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1180]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_7901,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | r1_lattices(sK7,sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),X1_55)
% 23.30/3.52      | ~ r2_hidden(X1_55,X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_7708,c_3042]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_12,plain,
% 23.30/3.52      ( r4_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f68]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1111,plain,
% 23.30/3.52      ( r4_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1112,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1111]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1116,plain,
% 23.30/3.52      ( m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | r4_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1112,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1117,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_1116]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3045,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK1(sK7,X0_55,X0_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1117]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4349,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3045]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_14911,plain,
% 23.30/3.52      ( ~ m1_subset_1(X1_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ r2_hidden(X1_55,X0_56)
% 23.30/3.52      | r1_lattices(sK7,sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),X1_55)
% 23.30/3.52      | r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_7901,c_4349]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_14912,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | r1_lattices(sK7,sK1(sK7,X0_55,a_2_9_lattice3(sK7,X0_56)),X1_55)
% 23.30/3.52      | ~ r2_hidden(X1_55,X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_14911]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_10,plain,
% 23.30/3.52      ( r4_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f70]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1153,plain,
% 23.30/3.52      ( r4_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1154,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ r1_lattices(sK7,sK1(sK7,X0,X1),X0)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1153]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1158,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ r1_lattices(sK7,sK1(sK7,X0,X1),X0)
% 23.30/3.52      | r4_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1154,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1159,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ r1_lattices(sK7,sK1(sK7,X0,X1),X0)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_1158]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3043,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | ~ r1_lattices(sK7,sK1(sK7,X0_55,X0_56),X0_55)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1159]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_15100,plain,
% 23.30/3.52      ( r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | ~ r2_hidden(X0_55,X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_14912,c_3043]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_15147,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
% 23.30/3.52      | ~ r2_hidden(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),X0_56)
% 23.30/3.52      | ~ m1_subset_1(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_9636,c_15100]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_15149,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
% 23.30/3.52      | ~ r2_hidden(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK9)
% 23.30/3.52      | ~ m1_subset_1(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_15147]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_13,plain,
% 23.30/3.52      ( ~ r4_lattice3(X0,X1,X2)
% 23.30/3.52      | r1_lattices(X0,X3,X1)
% 23.30/3.52      | ~ r2_hidden(X3,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f67]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1084,plain,
% 23.30/3.52      ( ~ r4_lattice3(X0,X1,X2)
% 23.30/3.52      | r1_lattices(X0,X3,X1)
% 23.30/3.52      | ~ r2_hidden(X3,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_13,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1085,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | r1_lattices(sK7,X2,X0)
% 23.30/3.52      | ~ r2_hidden(X2,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1084]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1089,plain,
% 23.30/3.52      ( ~ m1_subset_1(X2,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ r2_hidden(X2,X1)
% 23.30/3.52      | r1_lattices(sK7,X2,X0)
% 23.30/3.52      | ~ r4_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1085,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1090,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,X0,X1)
% 23.30/3.52      | r1_lattices(sK7,X2,X0)
% 23.30/3.52      | ~ r2_hidden(X2,X1)
% 23.30/3.52      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_1089]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3046,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | r1_lattices(sK7,X1_55,X0_55)
% 23.30/3.52      | ~ r2_hidden(X1_55,X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1090]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3871,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | r1_lattices(sK7,X1_55,X0_55)
% 23.30/3.52      | ~ r2_hidden(X1_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3046]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4004,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | r1_lattices(sK7,X0_55,sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
% 23.30/3.52      | ~ r2_hidden(X0_55,a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3871]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_9899,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | r1_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
% 23.30/3.52      | ~ r2_hidden(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),a_2_9_lattice3(sK7,X0_56))
% 23.30/3.52      | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4004]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_9901,plain,
% 23.30/3.52      ( ~ r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),a_2_9_lattice3(sK7,sK9))
% 23.30/3.52      | r1_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK4(sK7,a_2_9_lattice3(sK7,sK9)))
% 23.30/3.52      | ~ r2_hidden(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),a_2_9_lattice3(sK7,sK9))
% 23.30/3.52      | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_9899]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_6843,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
% 23.30/3.52      | m1_subset_1(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4455]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_6845,plain,
% 23.30/3.52      ( r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
% 23.30/3.52      | m1_subset_1(sK0(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_6843]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_26,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0)
% 23.30/3.52      | k16_lattice3(X0,X2) = X1 ),
% 23.30/3.52      inference(cnf_transformation,[],[f83]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_720,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | k16_lattice3(X0,X2) = X1
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_721,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7)
% 23.30/3.52      | v2_struct_0(sK7)
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_720]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_725,plain,
% 23.30/3.52      ( m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_721,c_35,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_726,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_725]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3056,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | m1_subset_1(sK6(sK7,X0_55,X0_56),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X0_56) = X0_55 ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_726]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_6410,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
% 23.30/3.52      | m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X1_56) = sK4(sK7,a_2_9_lattice3(sK7,X0_56)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3056]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_6412,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
% 23.30/3.52      | m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,sK9) = sK4(sK7,a_2_9_lattice3(sK7,sK9)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_6410]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_24,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0)
% 23.30/3.52      | k16_lattice3(X0,X2) = X1 ),
% 23.30/3.52      inference(cnf_transformation,[],[f85]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_768,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | k16_lattice3(X0,X2) = X1
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_769,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7)
% 23.30/3.52      | v2_struct_0(sK7)
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_768]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_773,plain,
% 23.30/3.52      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
% 23.30/3.52      | ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_769,c_35,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_774,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X1) = X0 ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_773]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3054,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | ~ r3_lattices(sK7,sK6(sK7,X0_55,X0_56),X0_55)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X0_56) = X0_55 ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_774]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4988,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56)
% 23.30/3.52      | ~ r3_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,X1_56) = sK4(sK7,a_2_9_lattice3(sK7,X0_56)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3054]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4994,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9)
% 23.30/3.52      | ~ r3_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK4(sK7,a_2_9_lattice3(sK7,sK9)))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7))
% 23.30/3.52      | k16_lattice3(sK7,sK9) = sK4(sK7,a_2_9_lattice3(sK7,sK9)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4988]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_0,plain,
% 23.30/3.52      ( ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0)
% 23.30/3.52      | v9_lattices(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f60]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4,plain,
% 23.30/3.52      ( ~ r1_lattices(X0,X1,X2)
% 23.30/3.52      | r3_lattices(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v6_lattices(X0)
% 23.30/3.52      | ~ v8_lattices(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v9_lattices(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f62]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_416,plain,
% 23.30/3.52      ( ~ r1_lattices(X0,X1,X2)
% 23.30/3.52      | r3_lattices(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ v6_lattices(X0)
% 23.30/3.52      | ~ v8_lattices(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0) ),
% 23.30/3.52      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_2,plain,
% 23.30/3.52      ( v6_lattices(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f58]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1,plain,
% 23.30/3.52      ( v8_lattices(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f59]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_420,plain,
% 23.30/3.52      ( ~ r1_lattices(X0,X1,X2)
% 23.30/3.52      | r3_lattices(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_416,c_2,c_1]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_630,plain,
% 23.30/3.52      ( ~ r1_lattices(X0,X1,X2)
% 23.30/3.52      | r3_lattices(X0,X1,X2)
% 23.30/3.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_420,c_34]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_631,plain,
% 23.30/3.52      ( ~ r1_lattices(sK7,X0,X1)
% 23.30/3.52      | r3_lattices(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 23.30/3.52      | ~ l3_lattices(sK7)
% 23.30/3.52      | v2_struct_0(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_630]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_635,plain,
% 23.30/3.52      ( ~ r1_lattices(sK7,X0,X1)
% 23.30/3.52      | r3_lattices(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_631,c_35,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_636,plain,
% 23.30/3.52      ( ~ r1_lattices(sK7,X0,X1)
% 23.30/3.52      | r3_lattices(sK7,X0,X1)
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_635]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3060,plain,
% 23.30/3.52      ( ~ r1_lattices(sK7,X0_55,X1_55)
% 23.30/3.52      | r3_lattices(sK7,X0_55,X1_55)
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_636]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4576,plain,
% 23.30/3.52      ( ~ r1_lattices(sK7,X0_55,sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
% 23.30/3.52      | r3_lattices(sK7,X0_55,sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3060]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4987,plain,
% 23.30/3.52      ( ~ r1_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
% 23.30/3.52      | r3_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),sK4(sK7,a_2_9_lattice3(sK7,X0_56)))
% 23.30/3.52      | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),X1_56),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4576]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4990,plain,
% 23.30/3.52      ( ~ r1_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK4(sK7,a_2_9_lattice3(sK7,sK9)))
% 23.30/3.52      | r3_lattices(sK7,sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),sK4(sK7,a_2_9_lattice3(sK7,sK9)))
% 23.30/3.52      | ~ m1_subset_1(sK6(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),sK9),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4987]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4244,plain,
% 23.30/3.52      ( m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,X0_56)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3049]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4246,plain,
% 23.30/3.52      ( m1_subset_1(sK4(sK7,a_2_9_lattice3(sK7,sK9)),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4244]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_18,plain,
% 23.30/3.52      ( r4_lattice3(X0,sK4(X0,X1),X1)
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f72]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1042,plain,
% 23.30/3.52      ( r4_lattice3(X0,sK4(X0,X1),X1)
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1043,plain,
% 23.30/3.52      ( r4_lattice3(sK7,sK4(sK7,X0),X0)
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_1042]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_1047,plain,
% 23.30/3.52      ( r4_lattice3(sK7,sK4(sK7,X0),X0) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_1043,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3048,plain,
% 23.30/3.52      ( r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_1047]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4005,plain,
% 23.30/3.52      ( r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,X0_56)),a_2_9_lattice3(sK7,X0_56)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3048]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_4011,plain,
% 23.30/3.52      ( r4_lattice3(sK7,sK4(sK7,a_2_9_lattice3(sK7,sK9)),a_2_9_lattice3(sK7,sK9)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_4005]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_27,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | ~ v10_lattices(X0) ),
% 23.30/3.52      inference(cnf_transformation,[],[f94]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_696,plain,
% 23.30/3.52      ( ~ r3_lattice3(X0,X1,X2)
% 23.30/3.52      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 23.30/3.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.30/3.52      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 23.30/3.52      | ~ v4_lattice3(X0)
% 23.30/3.52      | ~ l3_lattices(X0)
% 23.30/3.52      | v2_struct_0(X0)
% 23.30/3.52      | sK7 != X0 ),
% 23.30/3.52      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_697,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r3_lattices(sK7,X0,k16_lattice3(sK7,X1))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(k16_lattice3(sK7,X1),u1_struct_0(sK7))
% 23.30/3.52      | ~ v4_lattice3(sK7)
% 23.30/3.52      | ~ l3_lattices(sK7)
% 23.30/3.52      | v2_struct_0(sK7) ),
% 23.30/3.52      inference(unflattening,[status(thm)],[c_696]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_701,plain,
% 23.30/3.52      ( ~ m1_subset_1(k16_lattice3(sK7,X1),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | r3_lattices(sK7,X0,k16_lattice3(sK7,X1))
% 23.30/3.52      | ~ r3_lattice3(sK7,X0,X1) ),
% 23.30/3.52      inference(global_propositional_subsumption,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_697,c_35,c_33,c_32]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_702,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0,X1)
% 23.30/3.52      | r3_lattices(sK7,X0,k16_lattice3(sK7,X1))
% 23.30/3.52      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(k16_lattice3(sK7,X1),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(renaming,[status(thm)],[c_701]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3057,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 23.30/3.52      | r3_lattices(sK7,X0_55,k16_lattice3(sK7,X0_56))
% 23.30/3.52      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(k16_lattice3(sK7,X0_56),u1_struct_0(sK7)) ),
% 23.30/3.52      inference(subtyping,[status(esa)],[c_702]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_3094,plain,
% 23.30/3.52      ( ~ r3_lattice3(sK7,sK8,sK9)
% 23.30/3.52      | r3_lattices(sK7,sK8,k16_lattice3(sK7,sK9))
% 23.30/3.52      | ~ m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
% 23.30/3.52      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(instantiation,[status(thm)],[c_3057]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_29,negated_conjecture,
% 23.30/3.52      ( ~ r3_lattices(sK7,sK8,k16_lattice3(sK7,sK9)) ),
% 23.30/3.52      inference(cnf_transformation,[],[f92]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_30,negated_conjecture,
% 23.30/3.52      ( r3_lattice3(sK7,sK8,sK9) ),
% 23.30/3.52      inference(cnf_transformation,[],[f91]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(c_31,negated_conjecture,
% 23.30/3.52      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 23.30/3.52      inference(cnf_transformation,[],[f90]) ).
% 23.30/3.52  
% 23.30/3.52  cnf(contradiction,plain,
% 23.30/3.52      ( $false ),
% 23.30/3.52      inference(minisat,
% 23.30/3.52                [status(thm)],
% 23.30/3.52                [c_62344,c_48969,c_24400,c_15184,c_15149,c_9901,c_6845,
% 23.30/3.52                 c_6412,c_4994,c_4990,c_4246,c_4011,c_3094,c_29,c_30,
% 23.30/3.52                 c_31]) ).
% 23.30/3.52  
% 23.30/3.52  
% 23.30/3.52  % SZS output end CNFRefutation for theBenchmark.p
% 23.30/3.52  
% 23.30/3.52  ------                               Statistics
% 23.30/3.52  
% 23.30/3.52  ------ Selected
% 23.30/3.52  
% 23.30/3.52  total_time:                             2.817
% 23.30/3.52  
%------------------------------------------------------------------------------

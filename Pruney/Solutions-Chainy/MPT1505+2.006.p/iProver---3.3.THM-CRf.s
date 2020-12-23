%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:10 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  262 (3855 expanded)
%              Number of clauses        :  183 ( 950 expanded)
%              Number of leaves         :   19 (1112 expanded)
%              Depth                    :   32
%              Number of atoms          : 1224 (25706 expanded)
%              Number of equality atoms :  253 ( 863 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
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
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f53])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
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

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

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

fof(f85,plain,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_878,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_31])).

cnf(c_879,plain,
    ( r3_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_878])).

cnf(c_28,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_883,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_879,c_28])).

cnf(c_884,plain,
    ( r3_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_883])).

cnf(c_2628,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_884])).

cnf(c_3136,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
    | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2628])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_452,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_453,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | sK2(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_30,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_457,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | sK2(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_31,c_30,c_28])).

cnf(c_2645,plain,
    ( ~ r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54))
    | sK2(X0_53,sK4,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_3120,plain,
    ( sK2(X0_53,sK4,X0_54) = X0_53
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2645])).

cnf(c_5148,plain,
    ( sK2(sK0(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,X0_53,a_2_2_lattice3(sK4,X0_54))
    | r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3136,c_3120])).

cnf(c_24,plain,
    ( ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_485,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_486,plain,
    ( ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_490,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_31,c_30,c_28])).

cnf(c_2643,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54)) = k15_lattice3(sK4,X0_54) ),
    inference(subtyping,[status(esa)],[c_490])).

cnf(c_14,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_725,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_726,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_730,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_28])).

cnf(c_22,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_496,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_497,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_501,plain,
    ( ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_31,c_30,c_28])).

cnf(c_502,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_501])).

cnf(c_921,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_730,c_502])).

cnf(c_2626,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r3_lattices(sK4,X0_53,k16_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_921])).

cnf(c_3138,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) != iProver_top
    | r3_lattices(sK4,X0_53,k16_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2626])).

cnf(c_2635,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_730])).

cnf(c_3129,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2647,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3118,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

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
    inference(cnf_transformation,[],[f58])).

cnf(c_354,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_358,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_2,c_1])).

cnf(c_691,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_358,c_30])).

cnf(c_692,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_696,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_31,c_28])).

cnf(c_697,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_2636,plain,
    ( r1_lattices(sK4,X0_53,X1_53)
    | ~ r3_lattices(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_697])).

cnf(c_3128,plain,
    ( r1_lattices(sK4,X0_53,X1_53) = iProver_top
    | r3_lattices(sK4,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2636])).

cnf(c_3951,plain,
    ( r1_lattices(sK4,sK5,X0_53) = iProver_top
    | r3_lattices(sK4,sK5,X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3128])).

cnf(c_3996,plain,
    ( r1_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) = iProver_top
    | r3_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_3951])).

cnf(c_5668,plain,
    ( r3_lattice3(sK4,sK5,X0_54) != iProver_top
    | r1_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3138,c_3996])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8889,plain,
    ( r1_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) = iProver_top
    | r3_lattice3(sK4,sK5,X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5668,c_36])).

cnf(c_8890,plain,
    ( r3_lattice3(sK4,sK5,X0_54) != iProver_top
    | r1_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8889])).

cnf(c_8897,plain,
    ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,X0_54)) != iProver_top
    | r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2643,c_8890])).

cnf(c_13943,plain,
    ( sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54))
    | r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5148,c_8897])).

cnf(c_15277,plain,
    ( r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top
    | sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13943,c_36])).

cnf(c_15278,plain,
    ( sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54))
    | r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top ),
    inference(renaming,[status(thm)],[c_15277])).

cnf(c_3401,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2643,c_3129])).

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

cnf(c_390,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_2,c_1])).

cnf(c_667,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_390,c_30])).

cnf(c_668,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_672,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_668,c_31,c_28])).

cnf(c_673,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_672])).

cnf(c_2637,plain,
    ( ~ r1_lattices(sK4,X0_53,X1_53)
    | r3_lattices(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_673])).

cnf(c_3127,plain,
    ( r1_lattices(sK4,X0_53,X1_53) != iProver_top
    | r3_lattices(sK4,X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2637])).

cnf(c_3705,plain,
    ( r1_lattices(sK4,sK5,X0_53) != iProver_top
    | r3_lattices(sK4,sK5,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3127])).

cnf(c_3831,plain,
    ( r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) != iProver_top
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_3705])).

cnf(c_15285,plain,
    ( sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54))
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15278,c_3831])).

cnf(c_23,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_185,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_14])).

cnf(c_470,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_185,c_29])).

cnf(c_471,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_475,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_31,c_30,c_28])).

cnf(c_2644,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_475])).

cnf(c_3121,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2644])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_830,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_831,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_835,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_831,c_28])).

cnf(c_836,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_835])).

cnf(c_2630,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X0_53,X1_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_836])).

cnf(c_3134,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) != iProver_top
    | r1_lattices(sK4,X0_53,X1_53) = iProver_top
    | r2_hidden(X1_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2630])).

cnf(c_4537,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) != iProver_top
    | r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
    | r2_hidden(X0_53,X1_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_3134])).

cnf(c_6700,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_4537])).

cnf(c_3706,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) != iProver_top
    | r3_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_3127])).

cnf(c_6722,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6700,c_3706])).

cnf(c_25,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2649,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3116,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2649])).

cnf(c_16793,plain,
    ( r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,sK6) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6722,c_3116])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,plain,
    ( r2_hidden(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_38,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2676,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2644])).

cnf(c_2678,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2676])).

cnf(c_2701,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_2703,plain,
    ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2701])).

cnf(c_3334,plain,
    ( ~ r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_3335,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3334])).

cnf(c_3410,plain,
    ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),X0_54)
    | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r2_hidden(sK5,X0_54)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_3414,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),X0_54) != iProver_top
    | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
    | r2_hidden(sK5,X0_54) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3410])).

cnf(c_3416,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6) != iProver_top
    | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3414])).

cnf(c_16803,plain,
    ( r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16793,c_36,c_37,c_38,c_2678,c_2703,c_3335,c_3416])).

cnf(c_16808,plain,
    ( sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),sK4,sK6) = sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_15285,c_16803])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_434,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_439,plain,
    ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_31,c_30,c_28])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_439])).

cnf(c_2646,plain,
    ( ~ r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54))
    | m1_subset_1(sK2(X0_53,sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_3119,plain,
    ( r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
    | m1_subset_1(sK2(X0_53,sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2646])).

cnf(c_16901,plain,
    ( r2_hidden(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top
    | m1_subset_1(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16808,c_3119])).

cnf(c_2651,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2666,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_2679,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6)) = k15_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2643])).

cnf(c_3746,plain,
    ( k15_lattice3(sK4,sK6) = k15_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_2652,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_3454,plain,
    ( X0_53 != X1_53
    | X0_53 = k16_lattice3(sK4,X0_54)
    | k16_lattice3(sK4,X0_54) != X1_53 ),
    inference(instantiation,[status(thm)],[c_2652])).

cnf(c_3646,plain,
    ( X0_53 != k15_lattice3(sK4,X0_54)
    | X0_53 = k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54))
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54)) != k15_lattice3(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_3793,plain,
    ( k15_lattice3(sK4,X0_54) != k15_lattice3(sK4,X0_54)
    | k15_lattice3(sK4,X0_54) = k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54))
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54)) != k15_lattice3(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_3646])).

cnf(c_3795,plain,
    ( k15_lattice3(sK4,sK6) != k15_lattice3(sK4,sK6)
    | k15_lattice3(sK4,sK6) = k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6)) != k15_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_3793])).

cnf(c_2653,plain,
    ( ~ r3_lattices(X0_52,X0_53,X1_53)
    | r3_lattices(X0_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_3528,plain,
    ( ~ r3_lattices(sK4,X0_53,X1_53)
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | k15_lattice3(sK4,sK6) != X1_53
    | sK5 != X0_53 ),
    inference(instantiation,[status(thm)],[c_2653])).

cnf(c_4458,plain,
    ( ~ r3_lattices(sK4,X0_53,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6)))
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | k15_lattice3(sK4,sK6) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))
    | sK5 != X0_53 ),
    inference(instantiation,[status(thm)],[c_3528])).

cnf(c_4459,plain,
    ( k15_lattice3(sK4,sK6) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))
    | sK5 != X0_53
    | r3_lattices(sK4,X0_53,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))) != iProver_top
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4458])).

cnf(c_4461,plain,
    ( k15_lattice3(sK4,sK6) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))
    | sK5 != sK5
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) = iProver_top
    | r3_lattices(sK4,sK5,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4459])).

cnf(c_4839,plain,
    ( ~ r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,sK6))
    | r3_lattices(sK4,X0_53,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2626])).

cnf(c_4840,plain,
    ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,sK6)) != iProver_top
    | r3_lattices(sK4,X0_53,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4839])).

cnf(c_4842,plain,
    ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,sK6)) != iProver_top
    | r3_lattices(sK4,sK5,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4840])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_857,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_31])).

cnf(c_858,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_862,plain,
    ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_858,c_28])).

cnf(c_863,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_862])).

cnf(c_2629,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_863])).

cnf(c_6150,plain,
    ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,sK6))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_53,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2629])).

cnf(c_6156,plain,
    ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,X0_53,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6150])).

cnf(c_6158,plain,
    ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6156])).

cnf(c_17268,plain,
    ( m1_subset_1(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16901,c_36,c_37,c_38,c_2666,c_2678,c_2679,c_2703,c_3335,c_3416,c_3746,c_3795,c_4461,c_4842,c_6158])).

cnf(c_17277,plain,
    ( r1_lattices(sK4,sK5,sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6))) = iProver_top
    | r3_lattices(sK4,sK5,sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17268,c_3951])).

cnf(c_3914,plain,
    ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,X0_54))
    | r2_hidden(sK0(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)),a_2_2_lattice3(sK4,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_3919,plain,
    ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)) = iProver_top
    | r2_hidden(sK0(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)),a_2_2_lattice3(sK4,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3914])).

cnf(c_3921,plain,
    ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,sK6)) = iProver_top
    | r2_hidden(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3919])).

cnf(c_16,plain,
    ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_592,plain,
    ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_593,plain,
    ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_597,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | r4_lattice3(sK4,sK2(X0,sK4,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_31,c_30,c_28])).

cnf(c_598,plain,
    ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_597])).

cnf(c_2639,plain,
    ( r4_lattice3(sK4,sK2(X0_53,sK4,X0_54),X0_54)
    | ~ r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) ),
    inference(subtyping,[status(esa)],[c_598])).

cnf(c_3125,plain,
    ( r4_lattice3(sK4,sK2(X0_53,sK4,X0_54),X0_54) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2639])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_740,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_741,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_28])).

cnf(c_746,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_745])).

cnf(c_2634,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X1_53,X0_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_746])).

cnf(c_3130,plain,
    ( r4_lattice3(sK4,X0_53,X0_54) != iProver_top
    | r1_lattices(sK4,X1_53,X0_53) = iProver_top
    | r2_hidden(X1_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2634])).

cnf(c_4304,plain,
    ( r4_lattice3(sK4,sK2(X0_53,sK4,X0_54),X1_54) != iProver_top
    | r1_lattices(sK4,X1_53,sK2(X0_53,sK4,X0_54)) = iProver_top
    | r2_hidden(X1_53,X1_54) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3119,c_3130])).

cnf(c_8439,plain,
    ( r1_lattices(sK4,X0_53,sK2(X1_53,sK4,X0_54)) = iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top
    | r2_hidden(X1_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3125,c_4304])).

cnf(c_3830,plain,
    ( r1_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) != iProver_top
    | r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3119,c_3705])).

cnf(c_9044,plain,
    ( r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
    | r2_hidden(sK5,X0_54) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8439,c_3830])).

cnf(c_11477,plain,
    ( r2_hidden(sK5,X0_54) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
    | r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9044,c_36])).

cnf(c_11478,plain,
    ( r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
    | r2_hidden(sK5,X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_11477])).

cnf(c_3997,plain,
    ( r1_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
    | r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3119,c_3951])).

cnf(c_11486,plain,
    ( r1_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
    | r2_hidden(sK5,X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_11478,c_3997])).

cnf(c_16886,plain,
    ( r1_lattices(sK4,sK5,sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6))) = iProver_top
    | r2_hidden(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_16808,c_11486])).

cnf(c_17350,plain,
    ( r1_lattices(sK4,sK5,sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17277,c_36,c_37,c_38,c_2666,c_2678,c_2679,c_2703,c_3335,c_3416,c_3746,c_3795,c_3921,c_4461,c_4842,c_16886])).

cnf(c_6,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_899,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_31])).

cnf(c_900,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_904,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_28])).

cnf(c_905,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_904])).

cnf(c_2627,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_905])).

cnf(c_3137,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
    | r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2627])).

cnf(c_17355,plain,
    ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17350,c_3137])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17355,c_4842,c_4461,c_3795,c_3746,c_3416,c_3335,c_2703,c_2679,c_2678,c_2666,c_38,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:39:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.77/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.98  
% 3.77/0.98  ------  iProver source info
% 3.77/0.98  
% 3.77/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.98  git: non_committed_changes: false
% 3.77/0.98  git: last_make_outside_of_git: false
% 3.77/0.98  
% 3.77/0.98  ------ 
% 3.77/0.98  
% 3.77/0.98  ------ Input Options
% 3.77/0.98  
% 3.77/0.98  --out_options                           all
% 3.77/0.98  --tptp_safe_out                         true
% 3.77/0.98  --problem_path                          ""
% 3.77/0.98  --include_path                          ""
% 3.77/0.98  --clausifier                            res/vclausify_rel
% 3.77/0.98  --clausifier_options                    --mode clausify
% 3.77/0.98  --stdin                                 false
% 3.77/0.98  --stats_out                             all
% 3.77/0.98  
% 3.77/0.98  ------ General Options
% 3.77/0.98  
% 3.77/0.98  --fof                                   false
% 3.77/0.98  --time_out_real                         305.
% 3.77/0.98  --time_out_virtual                      -1.
% 3.77/0.98  --symbol_type_check                     false
% 3.77/0.98  --clausify_out                          false
% 3.77/0.98  --sig_cnt_out                           false
% 3.77/0.98  --trig_cnt_out                          false
% 3.77/0.98  --trig_cnt_out_tolerance                1.
% 3.77/0.98  --trig_cnt_out_sk_spl                   false
% 3.77/0.98  --abstr_cl_out                          false
% 3.77/0.98  
% 3.77/0.98  ------ Global Options
% 3.77/0.98  
% 3.77/0.98  --schedule                              default
% 3.77/0.98  --add_important_lit                     false
% 3.77/0.98  --prop_solver_per_cl                    1000
% 3.77/0.98  --min_unsat_core                        false
% 3.77/0.98  --soft_assumptions                      false
% 3.77/0.98  --soft_lemma_size                       3
% 3.77/0.98  --prop_impl_unit_size                   0
% 3.77/0.98  --prop_impl_unit                        []
% 3.77/0.98  --share_sel_clauses                     true
% 3.77/0.98  --reset_solvers                         false
% 3.77/0.98  --bc_imp_inh                            [conj_cone]
% 3.77/0.98  --conj_cone_tolerance                   3.
% 3.77/0.98  --extra_neg_conj                        none
% 3.77/0.98  --large_theory_mode                     true
% 3.77/0.98  --prolific_symb_bound                   200
% 3.77/0.98  --lt_threshold                          2000
% 3.77/0.98  --clause_weak_htbl                      true
% 3.77/0.98  --gc_record_bc_elim                     false
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing Options
% 3.77/0.98  
% 3.77/0.98  --preprocessing_flag                    true
% 3.77/0.98  --time_out_prep_mult                    0.1
% 3.77/0.98  --splitting_mode                        input
% 3.77/0.98  --splitting_grd                         true
% 3.77/0.98  --splitting_cvd                         false
% 3.77/0.98  --splitting_cvd_svl                     false
% 3.77/0.98  --splitting_nvd                         32
% 3.77/0.98  --sub_typing                            true
% 3.77/0.98  --prep_gs_sim                           true
% 3.77/0.98  --prep_unflatten                        true
% 3.77/0.98  --prep_res_sim                          true
% 3.77/0.98  --prep_upred                            true
% 3.77/0.98  --prep_sem_filter                       exhaustive
% 3.77/0.98  --prep_sem_filter_out                   false
% 3.77/0.98  --pred_elim                             true
% 3.77/0.98  --res_sim_input                         true
% 3.77/0.98  --eq_ax_congr_red                       true
% 3.77/0.98  --pure_diseq_elim                       true
% 3.77/0.98  --brand_transform                       false
% 3.77/0.98  --non_eq_to_eq                          false
% 3.77/0.98  --prep_def_merge                        true
% 3.77/0.98  --prep_def_merge_prop_impl              false
% 3.77/0.98  --prep_def_merge_mbd                    true
% 3.77/0.98  --prep_def_merge_tr_red                 false
% 3.77/0.98  --prep_def_merge_tr_cl                  false
% 3.77/0.98  --smt_preprocessing                     true
% 3.77/0.98  --smt_ac_axioms                         fast
% 3.77/0.98  --preprocessed_out                      false
% 3.77/0.98  --preprocessed_stats                    false
% 3.77/0.98  
% 3.77/0.98  ------ Abstraction refinement Options
% 3.77/0.98  
% 3.77/0.98  --abstr_ref                             []
% 3.77/0.98  --abstr_ref_prep                        false
% 3.77/0.98  --abstr_ref_until_sat                   false
% 3.77/0.98  --abstr_ref_sig_restrict                funpre
% 3.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.98  --abstr_ref_under                       []
% 3.77/0.98  
% 3.77/0.98  ------ SAT Options
% 3.77/0.98  
% 3.77/0.98  --sat_mode                              false
% 3.77/0.98  --sat_fm_restart_options                ""
% 3.77/0.98  --sat_gr_def                            false
% 3.77/0.98  --sat_epr_types                         true
% 3.77/0.98  --sat_non_cyclic_types                  false
% 3.77/0.98  --sat_finite_models                     false
% 3.77/0.98  --sat_fm_lemmas                         false
% 3.77/0.98  --sat_fm_prep                           false
% 3.77/0.98  --sat_fm_uc_incr                        true
% 3.77/0.98  --sat_out_model                         small
% 3.77/0.98  --sat_out_clauses                       false
% 3.77/0.98  
% 3.77/0.98  ------ QBF Options
% 3.77/0.98  
% 3.77/0.98  --qbf_mode                              false
% 3.77/0.98  --qbf_elim_univ                         false
% 3.77/0.98  --qbf_dom_inst                          none
% 3.77/0.98  --qbf_dom_pre_inst                      false
% 3.77/0.98  --qbf_sk_in                             false
% 3.77/0.98  --qbf_pred_elim                         true
% 3.77/0.98  --qbf_split                             512
% 3.77/0.98  
% 3.77/0.98  ------ BMC1 Options
% 3.77/0.98  
% 3.77/0.98  --bmc1_incremental                      false
% 3.77/0.98  --bmc1_axioms                           reachable_all
% 3.77/0.98  --bmc1_min_bound                        0
% 3.77/0.98  --bmc1_max_bound                        -1
% 3.77/0.98  --bmc1_max_bound_default                -1
% 3.77/0.98  --bmc1_symbol_reachability              true
% 3.77/0.98  --bmc1_property_lemmas                  false
% 3.77/0.98  --bmc1_k_induction                      false
% 3.77/0.98  --bmc1_non_equiv_states                 false
% 3.77/0.98  --bmc1_deadlock                         false
% 3.77/0.98  --bmc1_ucm                              false
% 3.77/0.98  --bmc1_add_unsat_core                   none
% 3.77/0.98  --bmc1_unsat_core_children              false
% 3.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.98  --bmc1_out_stat                         full
% 3.77/0.98  --bmc1_ground_init                      false
% 3.77/0.98  --bmc1_pre_inst_next_state              false
% 3.77/0.98  --bmc1_pre_inst_state                   false
% 3.77/0.98  --bmc1_pre_inst_reach_state             false
% 3.77/0.98  --bmc1_out_unsat_core                   false
% 3.77/0.98  --bmc1_aig_witness_out                  false
% 3.77/0.98  --bmc1_verbose                          false
% 3.77/0.98  --bmc1_dump_clauses_tptp                false
% 3.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.98  --bmc1_dump_file                        -
% 3.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.98  --bmc1_ucm_extend_mode                  1
% 3.77/0.98  --bmc1_ucm_init_mode                    2
% 3.77/0.98  --bmc1_ucm_cone_mode                    none
% 3.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.98  --bmc1_ucm_relax_model                  4
% 3.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.98  --bmc1_ucm_layered_model                none
% 3.77/0.98  --bmc1_ucm_max_lemma_size               10
% 3.77/0.98  
% 3.77/0.98  ------ AIG Options
% 3.77/0.98  
% 3.77/0.98  --aig_mode                              false
% 3.77/0.98  
% 3.77/0.98  ------ Instantiation Options
% 3.77/0.98  
% 3.77/0.98  --instantiation_flag                    true
% 3.77/0.98  --inst_sos_flag                         false
% 3.77/0.98  --inst_sos_phase                        true
% 3.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.98  --inst_lit_sel_side                     num_symb
% 3.77/0.98  --inst_solver_per_active                1400
% 3.77/0.98  --inst_solver_calls_frac                1.
% 3.77/0.98  --inst_passive_queue_type               priority_queues
% 3.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.98  --inst_passive_queues_freq              [25;2]
% 3.77/0.98  --inst_dismatching                      true
% 3.77/0.98  --inst_eager_unprocessed_to_passive     true
% 3.77/0.98  --inst_prop_sim_given                   true
% 3.77/0.98  --inst_prop_sim_new                     false
% 3.77/0.98  --inst_subs_new                         false
% 3.77/0.98  --inst_eq_res_simp                      false
% 3.77/0.98  --inst_subs_given                       false
% 3.77/0.98  --inst_orphan_elimination               true
% 3.77/0.98  --inst_learning_loop_flag               true
% 3.77/0.98  --inst_learning_start                   3000
% 3.77/0.98  --inst_learning_factor                  2
% 3.77/0.98  --inst_start_prop_sim_after_learn       3
% 3.77/0.98  --inst_sel_renew                        solver
% 3.77/0.98  --inst_lit_activity_flag                true
% 3.77/0.98  --inst_restr_to_given                   false
% 3.77/0.98  --inst_activity_threshold               500
% 3.77/0.98  --inst_out_proof                        true
% 3.77/0.98  
% 3.77/0.98  ------ Resolution Options
% 3.77/0.98  
% 3.77/0.98  --resolution_flag                       true
% 3.77/0.98  --res_lit_sel                           adaptive
% 3.77/0.98  --res_lit_sel_side                      none
% 3.77/0.98  --res_ordering                          kbo
% 3.77/0.98  --res_to_prop_solver                    active
% 3.77/0.98  --res_prop_simpl_new                    false
% 3.77/0.98  --res_prop_simpl_given                  true
% 3.77/0.98  --res_passive_queue_type                priority_queues
% 3.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.98  --res_passive_queues_freq               [15;5]
% 3.77/0.98  --res_forward_subs                      full
% 3.77/0.98  --res_backward_subs                     full
% 3.77/0.98  --res_forward_subs_resolution           true
% 3.77/0.98  --res_backward_subs_resolution          true
% 3.77/0.98  --res_orphan_elimination                true
% 3.77/0.98  --res_time_limit                        2.
% 3.77/0.98  --res_out_proof                         true
% 3.77/0.98  
% 3.77/0.98  ------ Superposition Options
% 3.77/0.98  
% 3.77/0.98  --superposition_flag                    true
% 3.77/0.98  --sup_passive_queue_type                priority_queues
% 3.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.98  --demod_completeness_check              fast
% 3.77/0.98  --demod_use_ground                      true
% 3.77/0.98  --sup_to_prop_solver                    passive
% 3.77/0.98  --sup_prop_simpl_new                    true
% 3.77/0.98  --sup_prop_simpl_given                  true
% 3.77/0.98  --sup_fun_splitting                     false
% 3.77/0.98  --sup_smt_interval                      50000
% 3.77/0.98  
% 3.77/0.98  ------ Superposition Simplification Setup
% 3.77/0.98  
% 3.77/0.98  --sup_indices_passive                   []
% 3.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.98  --sup_full_bw                           [BwDemod]
% 3.77/0.98  --sup_immed_triv                        [TrivRules]
% 3.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.98  --sup_immed_bw_main                     []
% 3.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/0.98  
% 3.77/0.98  ------ Combination Options
% 3.77/0.98  
% 3.77/0.98  --comb_res_mult                         3
% 3.77/0.98  --comb_sup_mult                         2
% 3.77/0.98  --comb_inst_mult                        10
% 3.77/0.98  
% 3.77/0.98  ------ Debug Options
% 3.77/0.98  
% 3.77/0.98  --dbg_backtrace                         false
% 3.77/0.98  --dbg_dump_prop_clauses                 false
% 3.77/0.98  --dbg_dump_prop_clauses_file            -
% 3.77/0.98  --dbg_out_stat                          false
% 3.77/0.98  ------ Parsing...
% 3.77/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.98  ------ Proving...
% 3.77/0.98  ------ Problem Properties 
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  clauses                                 24
% 3.77/0.98  conjectures                             3
% 3.77/0.98  EPR                                     1
% 3.77/0.98  Horn                                    18
% 3.77/0.98  unary                                   5
% 3.77/0.98  binary                                  4
% 3.77/0.98  lits                                    67
% 3.77/0.98  lits eq                                 5
% 3.77/0.98  fd_pure                                 0
% 3.77/0.98  fd_pseudo                               0
% 3.77/0.98  fd_cond                                 0
% 3.77/0.98  fd_pseudo_cond                          3
% 3.77/0.98  AC symbols                              0
% 3.77/0.98  
% 3.77/0.98  ------ Schedule dynamic 5 is on 
% 3.77/0.98  
% 3.77/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  ------ 
% 3.77/0.98  Current options:
% 3.77/0.98  ------ 
% 3.77/0.98  
% 3.77/0.98  ------ Input Options
% 3.77/0.98  
% 3.77/0.98  --out_options                           all
% 3.77/0.98  --tptp_safe_out                         true
% 3.77/0.98  --problem_path                          ""
% 3.77/0.98  --include_path                          ""
% 3.77/0.98  --clausifier                            res/vclausify_rel
% 3.77/0.98  --clausifier_options                    --mode clausify
% 3.77/0.98  --stdin                                 false
% 3.77/0.98  --stats_out                             all
% 3.77/0.98  
% 3.77/0.98  ------ General Options
% 3.77/0.98  
% 3.77/0.98  --fof                                   false
% 3.77/0.98  --time_out_real                         305.
% 3.77/0.98  --time_out_virtual                      -1.
% 3.77/0.98  --symbol_type_check                     false
% 3.77/0.98  --clausify_out                          false
% 3.77/0.98  --sig_cnt_out                           false
% 3.77/0.98  --trig_cnt_out                          false
% 3.77/0.98  --trig_cnt_out_tolerance                1.
% 3.77/0.98  --trig_cnt_out_sk_spl                   false
% 3.77/0.98  --abstr_cl_out                          false
% 3.77/0.98  
% 3.77/0.98  ------ Global Options
% 3.77/0.98  
% 3.77/0.98  --schedule                              default
% 3.77/0.98  --add_important_lit                     false
% 3.77/0.98  --prop_solver_per_cl                    1000
% 3.77/0.98  --min_unsat_core                        false
% 3.77/0.98  --soft_assumptions                      false
% 3.77/0.98  --soft_lemma_size                       3
% 3.77/0.98  --prop_impl_unit_size                   0
% 3.77/0.98  --prop_impl_unit                        []
% 3.77/0.98  --share_sel_clauses                     true
% 3.77/0.98  --reset_solvers                         false
% 3.77/0.98  --bc_imp_inh                            [conj_cone]
% 3.77/0.98  --conj_cone_tolerance                   3.
% 3.77/0.98  --extra_neg_conj                        none
% 3.77/0.98  --large_theory_mode                     true
% 3.77/0.98  --prolific_symb_bound                   200
% 3.77/0.98  --lt_threshold                          2000
% 3.77/0.98  --clause_weak_htbl                      true
% 3.77/0.98  --gc_record_bc_elim                     false
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing Options
% 3.77/0.98  
% 3.77/0.98  --preprocessing_flag                    true
% 3.77/0.98  --time_out_prep_mult                    0.1
% 3.77/0.98  --splitting_mode                        input
% 3.77/0.98  --splitting_grd                         true
% 3.77/0.98  --splitting_cvd                         false
% 3.77/0.98  --splitting_cvd_svl                     false
% 3.77/0.98  --splitting_nvd                         32
% 3.77/0.98  --sub_typing                            true
% 3.77/0.98  --prep_gs_sim                           true
% 3.77/0.98  --prep_unflatten                        true
% 3.77/0.98  --prep_res_sim                          true
% 3.77/0.98  --prep_upred                            true
% 3.77/0.98  --prep_sem_filter                       exhaustive
% 3.77/0.98  --prep_sem_filter_out                   false
% 3.77/0.98  --pred_elim                             true
% 3.77/0.98  --res_sim_input                         true
% 3.77/0.98  --eq_ax_congr_red                       true
% 3.77/0.98  --pure_diseq_elim                       true
% 3.77/0.98  --brand_transform                       false
% 3.77/0.98  --non_eq_to_eq                          false
% 3.77/0.98  --prep_def_merge                        true
% 3.77/0.98  --prep_def_merge_prop_impl              false
% 3.77/0.98  --prep_def_merge_mbd                    true
% 3.77/0.98  --prep_def_merge_tr_red                 false
% 3.77/0.98  --prep_def_merge_tr_cl                  false
% 3.77/0.98  --smt_preprocessing                     true
% 3.77/0.98  --smt_ac_axioms                         fast
% 3.77/0.98  --preprocessed_out                      false
% 3.77/0.98  --preprocessed_stats                    false
% 3.77/0.98  
% 3.77/0.98  ------ Abstraction refinement Options
% 3.77/0.98  
% 3.77/0.98  --abstr_ref                             []
% 3.77/0.98  --abstr_ref_prep                        false
% 3.77/0.98  --abstr_ref_until_sat                   false
% 3.77/0.98  --abstr_ref_sig_restrict                funpre
% 3.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.98  --abstr_ref_under                       []
% 3.77/0.98  
% 3.77/0.98  ------ SAT Options
% 3.77/0.98  
% 3.77/0.98  --sat_mode                              false
% 3.77/0.98  --sat_fm_restart_options                ""
% 3.77/0.98  --sat_gr_def                            false
% 3.77/0.98  --sat_epr_types                         true
% 3.77/0.98  --sat_non_cyclic_types                  false
% 3.77/0.98  --sat_finite_models                     false
% 3.77/0.98  --sat_fm_lemmas                         false
% 3.77/0.98  --sat_fm_prep                           false
% 3.77/0.98  --sat_fm_uc_incr                        true
% 3.77/0.98  --sat_out_model                         small
% 3.77/0.98  --sat_out_clauses                       false
% 3.77/0.98  
% 3.77/0.98  ------ QBF Options
% 3.77/0.98  
% 3.77/0.98  --qbf_mode                              false
% 3.77/0.98  --qbf_elim_univ                         false
% 3.77/0.98  --qbf_dom_inst                          none
% 3.77/0.98  --qbf_dom_pre_inst                      false
% 3.77/0.98  --qbf_sk_in                             false
% 3.77/0.98  --qbf_pred_elim                         true
% 3.77/0.98  --qbf_split                             512
% 3.77/0.98  
% 3.77/0.98  ------ BMC1 Options
% 3.77/0.98  
% 3.77/0.98  --bmc1_incremental                      false
% 3.77/0.98  --bmc1_axioms                           reachable_all
% 3.77/0.98  --bmc1_min_bound                        0
% 3.77/0.98  --bmc1_max_bound                        -1
% 3.77/0.98  --bmc1_max_bound_default                -1
% 3.77/0.98  --bmc1_symbol_reachability              true
% 3.77/0.98  --bmc1_property_lemmas                  false
% 3.77/0.98  --bmc1_k_induction                      false
% 3.77/0.98  --bmc1_non_equiv_states                 false
% 3.77/0.98  --bmc1_deadlock                         false
% 3.77/0.98  --bmc1_ucm                              false
% 3.77/0.98  --bmc1_add_unsat_core                   none
% 3.77/0.98  --bmc1_unsat_core_children              false
% 3.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.98  --bmc1_out_stat                         full
% 3.77/0.98  --bmc1_ground_init                      false
% 3.77/0.98  --bmc1_pre_inst_next_state              false
% 3.77/0.98  --bmc1_pre_inst_state                   false
% 3.77/0.98  --bmc1_pre_inst_reach_state             false
% 3.77/0.98  --bmc1_out_unsat_core                   false
% 3.77/0.98  --bmc1_aig_witness_out                  false
% 3.77/0.98  --bmc1_verbose                          false
% 3.77/0.98  --bmc1_dump_clauses_tptp                false
% 3.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.98  --bmc1_dump_file                        -
% 3.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.98  --bmc1_ucm_extend_mode                  1
% 3.77/0.98  --bmc1_ucm_init_mode                    2
% 3.77/0.98  --bmc1_ucm_cone_mode                    none
% 3.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.98  --bmc1_ucm_relax_model                  4
% 3.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.98  --bmc1_ucm_layered_model                none
% 3.77/0.98  --bmc1_ucm_max_lemma_size               10
% 3.77/0.98  
% 3.77/0.98  ------ AIG Options
% 3.77/0.98  
% 3.77/0.98  --aig_mode                              false
% 3.77/0.98  
% 3.77/0.98  ------ Instantiation Options
% 3.77/0.98  
% 3.77/0.98  --instantiation_flag                    true
% 3.77/0.98  --inst_sos_flag                         false
% 3.77/0.98  --inst_sos_phase                        true
% 3.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.98  --inst_lit_sel_side                     none
% 3.77/0.98  --inst_solver_per_active                1400
% 3.77/0.98  --inst_solver_calls_frac                1.
% 3.77/0.98  --inst_passive_queue_type               priority_queues
% 3.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.98  --inst_passive_queues_freq              [25;2]
% 3.77/0.98  --inst_dismatching                      true
% 3.77/0.98  --inst_eager_unprocessed_to_passive     true
% 3.77/0.98  --inst_prop_sim_given                   true
% 3.77/0.98  --inst_prop_sim_new                     false
% 3.77/0.98  --inst_subs_new                         false
% 3.77/0.98  --inst_eq_res_simp                      false
% 3.77/0.98  --inst_subs_given                       false
% 3.77/0.98  --inst_orphan_elimination               true
% 3.77/0.98  --inst_learning_loop_flag               true
% 3.77/0.98  --inst_learning_start                   3000
% 3.77/0.98  --inst_learning_factor                  2
% 3.77/0.98  --inst_start_prop_sim_after_learn       3
% 3.77/0.98  --inst_sel_renew                        solver
% 3.77/0.98  --inst_lit_activity_flag                true
% 3.77/0.98  --inst_restr_to_given                   false
% 3.77/0.98  --inst_activity_threshold               500
% 3.77/0.98  --inst_out_proof                        true
% 3.77/0.98  
% 3.77/0.98  ------ Resolution Options
% 3.77/0.98  
% 3.77/0.98  --resolution_flag                       false
% 3.77/0.98  --res_lit_sel                           adaptive
% 3.77/0.98  --res_lit_sel_side                      none
% 3.77/0.98  --res_ordering                          kbo
% 3.77/0.98  --res_to_prop_solver                    active
% 3.77/0.98  --res_prop_simpl_new                    false
% 3.77/0.98  --res_prop_simpl_given                  true
% 3.77/0.98  --res_passive_queue_type                priority_queues
% 3.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.98  --res_passive_queues_freq               [15;5]
% 3.77/0.98  --res_forward_subs                      full
% 3.77/0.98  --res_backward_subs                     full
% 3.77/0.98  --res_forward_subs_resolution           true
% 3.77/0.98  --res_backward_subs_resolution          true
% 3.77/0.98  --res_orphan_elimination                true
% 3.77/0.98  --res_time_limit                        2.
% 3.77/0.98  --res_out_proof                         true
% 3.77/0.98  
% 3.77/0.98  ------ Superposition Options
% 3.77/0.98  
% 3.77/0.98  --superposition_flag                    true
% 3.77/0.98  --sup_passive_queue_type                priority_queues
% 3.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.98  --demod_completeness_check              fast
% 3.77/0.98  --demod_use_ground                      true
% 3.77/0.98  --sup_to_prop_solver                    passive
% 3.77/0.98  --sup_prop_simpl_new                    true
% 3.77/0.98  --sup_prop_simpl_given                  true
% 3.77/0.98  --sup_fun_splitting                     false
% 3.77/0.98  --sup_smt_interval                      50000
% 3.77/0.98  
% 3.77/0.98  ------ Superposition Simplification Setup
% 3.77/0.98  
% 3.77/0.98  --sup_indices_passive                   []
% 3.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.98  --sup_full_bw                           [BwDemod]
% 3.77/0.98  --sup_immed_triv                        [TrivRules]
% 3.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.98  --sup_immed_bw_main                     []
% 3.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.77/0.98  
% 3.77/0.98  ------ Combination Options
% 3.77/0.98  
% 3.77/0.98  --comb_res_mult                         3
% 3.77/0.98  --comb_sup_mult                         2
% 3.77/0.98  --comb_inst_mult                        10
% 3.77/0.98  
% 3.77/0.98  ------ Debug Options
% 3.77/0.98  
% 3.77/0.98  --dbg_backtrace                         false
% 3.77/0.98  --dbg_dump_prop_clauses                 false
% 3.77/0.98  --dbg_dump_prop_clauses_file            -
% 3.77/0.98  --dbg_out_stat                          false
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  ------ Proving...
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  % SZS status Theorem for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  fof(f3,axiom,(
% 3.77/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f18,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f3])).
% 3.77/0.98  
% 3.77/0.98  fof(f19,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(flattening,[],[f18])).
% 3.77/0.98  
% 3.77/0.98  fof(f33,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(nnf_transformation,[],[f19])).
% 3.77/0.98  
% 3.77/0.98  fof(f34,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(rectify,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  fof(f35,plain,(
% 3.77/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f36,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.77/0.98  
% 3.77/0.98  fof(f62,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f36])).
% 3.77/0.98  
% 3.77/0.98  fof(f9,conjecture,(
% 3.77/0.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f10,negated_conjecture,(
% 3.77/0.98    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 3.77/0.98    inference(negated_conjecture,[],[f9])).
% 3.77/0.98  
% 3.77/0.98  fof(f30,plain,(
% 3.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f10])).
% 3.77/0.98  
% 3.77/0.98  fof(f31,plain,(
% 3.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.77/0.98    inference(flattening,[],[f30])).
% 3.77/0.98  
% 3.77/0.98  fof(f52,plain,(
% 3.77/0.98    ( ! [X0,X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK6),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,sK6))) & r2_hidden(X1,sK6))) )),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f51,plain,(
% 3.77/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),sK5) | ~r3_lattices(X0,sK5,k15_lattice3(X0,X2))) & r2_hidden(sK5,X2)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f50,plain,(
% 3.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK4,k16_lattice3(sK4,X2),X1) | ~r3_lattices(sK4,X1,k15_lattice3(sK4,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f53,plain,(
% 3.77/0.98    (((~r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) | ~r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))) & r2_hidden(sK5,sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 3.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f52,f51,f50])).
% 3.77/0.98  
% 3.77/0.98  fof(f79,plain,(
% 3.77/0.98    ~v2_struct_0(sK4)),
% 3.77/0.98    inference(cnf_transformation,[],[f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f82,plain,(
% 3.77/0.98    l3_lattices(sK4)),
% 3.77/0.98    inference(cnf_transformation,[],[f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f6,axiom,(
% 3.77/0.98    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f24,plain,(
% 3.77/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 3.77/0.98    inference(ennf_transformation,[],[f6])).
% 3.77/0.98  
% 3.77/0.98  fof(f25,plain,(
% 3.77/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.77/0.98    inference(flattening,[],[f24])).
% 3.77/0.98  
% 3.77/0.98  fof(f41,plain,(
% 3.77/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.77/0.98    inference(nnf_transformation,[],[f25])).
% 3.77/0.98  
% 3.77/0.98  fof(f42,plain,(
% 3.77/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.77/0.98    inference(rectify,[],[f41])).
% 3.77/0.98  
% 3.77/0.98  fof(f43,plain,(
% 3.77/0.98    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f44,plain,(
% 3.77/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 3.77/0.98  
% 3.77/0.98  fof(f70,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f44])).
% 3.77/0.98  
% 3.77/0.98  fof(f81,plain,(
% 3.77/0.98    v4_lattice3(sK4)),
% 3.77/0.98    inference(cnf_transformation,[],[f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f80,plain,(
% 3.77/0.98    v10_lattices(sK4)),
% 3.77/0.98    inference(cnf_transformation,[],[f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f8,axiom,(
% 3.77/0.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f28,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f8])).
% 3.77/0.98  
% 3.77/0.98  fof(f29,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(flattening,[],[f28])).
% 3.77/0.98  
% 3.77/0.98  fof(f78,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f29])).
% 3.77/0.98  
% 3.77/0.98  fof(f5,axiom,(
% 3.77/0.98    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f22,plain,(
% 3.77/0.98    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f5])).
% 3.77/0.98  
% 3.77/0.98  fof(f23,plain,(
% 3.77/0.98    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(flattening,[],[f22])).
% 3.77/0.98  
% 3.77/0.98  fof(f68,plain,(
% 3.77/0.98    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f23])).
% 3.77/0.98  
% 3.77/0.98  fof(f7,axiom,(
% 3.77/0.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f26,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f7])).
% 3.77/0.98  
% 3.77/0.98  fof(f27,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(flattening,[],[f26])).
% 3.77/0.98  
% 3.77/0.98  fof(f45,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(nnf_transformation,[],[f27])).
% 3.77/0.98  
% 3.77/0.98  fof(f46,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(flattening,[],[f45])).
% 3.77/0.98  
% 3.77/0.98  fof(f47,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(rectify,[],[f46])).
% 3.77/0.98  
% 3.77/0.98  fof(f48,plain,(
% 3.77/0.98    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f49,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 3.77/0.98  
% 3.77/0.98  fof(f74,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f49])).
% 3.77/0.98  
% 3.77/0.98  fof(f87,plain,(
% 3.77/0.98    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(equality_resolution,[],[f74])).
% 3.77/0.98  
% 3.77/0.98  fof(f83,plain,(
% 3.77/0.98    m1_subset_1(sK5,u1_struct_0(sK4))),
% 3.77/0.98    inference(cnf_transformation,[],[f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f1,axiom,(
% 3.77/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f11,plain,(
% 3.77/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.77/0.98    inference(pure_predicate_removal,[],[f1])).
% 3.77/0.98  
% 3.77/0.98  fof(f12,plain,(
% 3.77/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.77/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.77/0.98  
% 3.77/0.98  fof(f13,plain,(
% 3.77/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 3.77/0.98    inference(pure_predicate_removal,[],[f12])).
% 3.77/0.98  
% 3.77/0.98  fof(f14,plain,(
% 3.77/0.98    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.77/0.98    inference(ennf_transformation,[],[f13])).
% 3.77/0.98  
% 3.77/0.98  fof(f15,plain,(
% 3.77/0.98    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.77/0.98    inference(flattening,[],[f14])).
% 3.77/0.98  
% 3.77/0.98  fof(f57,plain,(
% 3.77/0.98    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f15])).
% 3.77/0.98  
% 3.77/0.98  fof(f2,axiom,(
% 3.77/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f16,plain,(
% 3.77/0.98    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f2])).
% 3.77/0.98  
% 3.77/0.98  fof(f17,plain,(
% 3.77/0.98    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(flattening,[],[f16])).
% 3.77/0.98  
% 3.77/0.98  fof(f32,plain,(
% 3.77/0.98    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(nnf_transformation,[],[f17])).
% 3.77/0.98  
% 3.77/0.98  fof(f58,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f32])).
% 3.77/0.98  
% 3.77/0.98  fof(f55,plain,(
% 3.77/0.98    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f15])).
% 3.77/0.98  
% 3.77/0.98  fof(f56,plain,(
% 3.77/0.98    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f15])).
% 3.77/0.98  
% 3.77/0.98  fof(f59,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f32])).
% 3.77/0.98  
% 3.77/0.98  fof(f73,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f49])).
% 3.77/0.98  
% 3.77/0.98  fof(f88,plain,(
% 3.77/0.98    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(equality_resolution,[],[f73])).
% 3.77/0.98  
% 3.77/0.98  fof(f60,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f36])).
% 3.77/0.98  
% 3.77/0.98  fof(f85,plain,(
% 3.77/0.98    ~r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) | ~r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))),
% 3.77/0.98    inference(cnf_transformation,[],[f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f84,plain,(
% 3.77/0.98    r2_hidden(sK5,sK6)),
% 3.77/0.98    inference(cnf_transformation,[],[f53])).
% 3.77/0.98  
% 3.77/0.98  fof(f69,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f44])).
% 3.77/0.98  
% 3.77/0.98  fof(f61,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f36])).
% 3.77/0.98  
% 3.77/0.98  fof(f71,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK2(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f44])).
% 3.77/0.98  
% 3.77/0.98  fof(f4,axiom,(
% 3.77/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f20,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f4])).
% 3.77/0.98  
% 3.77/0.98  fof(f21,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(flattening,[],[f20])).
% 3.77/0.98  
% 3.77/0.98  fof(f37,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(nnf_transformation,[],[f21])).
% 3.77/0.98  
% 3.77/0.98  fof(f38,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(rectify,[],[f37])).
% 3.77/0.98  
% 3.77/0.98  fof(f39,plain,(
% 3.77/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f40,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.77/0.98  
% 3.77/0.98  fof(f64,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f40])).
% 3.77/0.98  
% 3.77/0.98  fof(f63,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f36])).
% 3.77/0.98  
% 3.77/0.98  cnf(c_7,plain,
% 3.77/0.98      ( r3_lattice3(X0,X1,X2)
% 3.77/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_31,negated_conjecture,
% 3.77/0.98      ( ~ v2_struct_0(sK4) ),
% 3.77/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_878,plain,
% 3.77/0.98      ( r3_lattice3(X0,X1,X2)
% 3.77/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_31]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_879,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | r2_hidden(sK0(sK4,X0,X1),X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_878]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_28,negated_conjecture,
% 3.77/0.98      ( l3_lattices(sK4) ),
% 3.77/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_883,plain,
% 3.77/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | r2_hidden(sK0(sK4,X0,X1),X1)
% 3.77/0.98      | r3_lattice3(sK4,X0,X1) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_879,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_884,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | r2_hidden(sK0(sK4,X0,X1),X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_883]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2628,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,X0_54)
% 3.77/0.98      | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54)
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_884]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3136,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
% 3.77/0.98      | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2628]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_17,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.77/0.98      | ~ v4_lattice3(X1)
% 3.77/0.98      | ~ l3_lattices(X1)
% 3.77/0.98      | v2_struct_0(X1)
% 3.77/0.98      | ~ v10_lattices(X1)
% 3.77/0.98      | sK2(X0,X1,X2) = X0 ),
% 3.77/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_29,negated_conjecture,
% 3.77/0.98      ( v4_lattice3(sK4) ),
% 3.77/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_452,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.77/0.98      | ~ l3_lattices(X1)
% 3.77/0.98      | v2_struct_0(X1)
% 3.77/0.98      | ~ v10_lattices(X1)
% 3.77/0.98      | sK2(X0,X1,X2) = X0
% 3.77/0.98      | sK4 != X1 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_453,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.77/0.98      | ~ l3_lattices(sK4)
% 3.77/0.98      | v2_struct_0(sK4)
% 3.77/0.98      | ~ v10_lattices(sK4)
% 3.77/0.98      | sK2(X0,sK4,X1) = X0 ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_452]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_30,negated_conjecture,
% 3.77/0.98      ( v10_lattices(sK4) ),
% 3.77/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_457,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) | sK2(X0,sK4,X1) = X0 ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_453,c_31,c_30,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2645,plain,
% 3.77/0.98      ( ~ r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | sK2(X0_53,sK4,X0_54) = X0_53 ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_457]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3120,plain,
% 3.77/0.98      ( sK2(X0_53,sK4,X0_54) = X0_53
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2645]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5148,plain,
% 3.77/0.98      ( sK2(sK0(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,X0_53,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3136,c_3120]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_24,plain,
% 3.77/0.98      ( ~ v4_lattice3(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0)
% 3.77/0.98      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
% 3.77/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_485,plain,
% 3.77/0.98      ( ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0)
% 3.77/0.98      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_486,plain,
% 3.77/0.98      ( ~ l3_lattices(sK4)
% 3.77/0.98      | v2_struct_0(sK4)
% 3.77/0.98      | ~ v10_lattices(sK4)
% 3.77/0.98      | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_485]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_490,plain,
% 3.77/0.98      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_486,c_31,c_30,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2643,plain,
% 3.77/0.98      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54)) = k15_lattice3(sK4,X0_54) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_490]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_14,plain,
% 3.77/0.98      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_725,plain,
% 3.77/0.98      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_726,plain,
% 3.77/0.98      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_725]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_730,plain,
% 3.77/0.98      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_726,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_22,plain,
% 3.77/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.77/0.98      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 3.77/0.98      | ~ v4_lattice3(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_496,plain,
% 3.77/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.77/0.98      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_497,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4)
% 3.77/0.98      | v2_struct_0(sK4)
% 3.77/0.98      | ~ v10_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_496]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_501,plain,
% 3.77/0.98      ( ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.77/0.98      | ~ r3_lattice3(sK4,X0,X1) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_497,c_31,c_30,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_502,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_501]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_921,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(backward_subsumption_resolution,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_730,c_502]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2626,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 3.77/0.98      | r3_lattices(sK4,X0_53,k16_lattice3(sK4,X0_54))
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_921]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3138,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,X0_54) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,X0_53,k16_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2626]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2635,plain,
% 3.77/0.98      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_730]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3129,plain,
% 3.77/0.98      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_27,negated_conjecture,
% 3.77/0.98      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2647,negated_conjecture,
% 3.77/0.98      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_27]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3118,plain,
% 3.77/0.98      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_0,plain,
% 3.77/0.98      ( ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0)
% 3.77/0.98      | v9_lattices(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5,plain,
% 3.77/0.98      ( r1_lattices(X0,X1,X2)
% 3.77/0.98      | ~ r3_lattices(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ v6_lattices(X0)
% 3.77/0.98      | ~ v8_lattices(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v9_lattices(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_354,plain,
% 3.77/0.98      ( r1_lattices(X0,X1,X2)
% 3.77/0.98      | ~ r3_lattices(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ v6_lattices(X0)
% 3.77/0.98      | ~ v8_lattices(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(resolution,[status(thm)],[c_0,c_5]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2,plain,
% 3.77/0.98      ( v6_lattices(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1,plain,
% 3.77/0.98      ( v8_lattices(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_358,plain,
% 3.77/0.98      ( r1_lattices(X0,X1,X2)
% 3.77/0.98      | ~ r3_lattices(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_354,c_2,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_691,plain,
% 3.77/0.98      ( r1_lattices(X0,X1,X2)
% 3.77/0.98      | ~ r3_lattices(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_358,c_30]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_692,plain,
% 3.77/0.98      ( r1_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ r3_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4)
% 3.77/0.98      | v2_struct_0(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_691]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_696,plain,
% 3.77/0.98      ( r1_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ r3_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_692,c_31,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_697,plain,
% 3.77/0.98      ( r1_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ r3_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_696]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2636,plain,
% 3.77/0.98      ( r1_lattices(sK4,X0_53,X1_53)
% 3.77/0.98      | ~ r3_lattices(sK4,X0_53,X1_53)
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_697]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3128,plain,
% 3.77/0.98      ( r1_lattices(sK4,X0_53,X1_53) = iProver_top
% 3.77/0.98      | r3_lattices(sK4,X0_53,X1_53) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.77/0.98      | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2636]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3951,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,X0_53) = iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,X0_53) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3118,c_3128]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3996,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3129,c_3951]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5668,plain,
% 3.77/0.98      ( r3_lattice3(sK4,sK5,X0_54) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3138,c_3996]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_36,plain,
% 3.77/0.98      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8889,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | r3_lattice3(sK4,sK5,X0_54) != iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_5668,c_36]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8890,plain,
% 3.77/0.98      ( r3_lattice3(sK4,sK5,X0_54) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,sK5,k16_lattice3(sK4,X0_54)) = iProver_top ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_8889]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8897,plain,
% 3.77/0.98      ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_2643,c_8890]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_13943,plain,
% 3.77/0.98      ( sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_5148,c_8897]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_15277,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_13943,c_36]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_15278,plain,
% 3.77/0.98      ( sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_15277]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3401,plain,
% 3.77/0.98      ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_2643,c_3129]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4,plain,
% 3.77/0.98      ( ~ r1_lattices(X0,X1,X2)
% 3.77/0.98      | r3_lattices(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ v6_lattices(X0)
% 3.77/0.98      | ~ v8_lattices(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v9_lattices(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_386,plain,
% 3.77/0.98      ( ~ r1_lattices(X0,X1,X2)
% 3.77/0.98      | r3_lattices(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ v6_lattices(X0)
% 3.77/0.98      | ~ v8_lattices(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_390,plain,
% 3.77/0.98      ( ~ r1_lattices(X0,X1,X2)
% 3.77/0.98      | r3_lattices(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_386,c_2,c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_667,plain,
% 3.77/0.98      ( ~ r1_lattices(X0,X1,X2)
% 3.77/0.98      | r3_lattices(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_390,c_30]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_668,plain,
% 3.77/0.98      ( ~ r1_lattices(sK4,X0,X1)
% 3.77/0.98      | r3_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4)
% 3.77/0.98      | v2_struct_0(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_667]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_672,plain,
% 3.77/0.98      ( ~ r1_lattices(sK4,X0,X1)
% 3.77/0.98      | r3_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_668,c_31,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_673,plain,
% 3.77/0.98      ( ~ r1_lattices(sK4,X0,X1)
% 3.77/0.98      | r3_lattices(sK4,X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_672]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2637,plain,
% 3.77/0.98      ( ~ r1_lattices(sK4,X0_53,X1_53)
% 3.77/0.98      | r3_lattices(sK4,X0_53,X1_53)
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_673]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3127,plain,
% 3.77/0.98      ( r1_lattices(sK4,X0_53,X1_53) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,X0_53,X1_53) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.77/0.98      | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2637]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3705,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,X0_53) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,X0_53) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3118,c_3127]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3831,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3401,c_3705]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_15285,plain,
% 3.77/0.98      ( sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54)),sK4,X0_54) = sK0(sK4,sK5,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | r3_lattices(sK4,sK5,k15_lattice3(sK4,X0_54)) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_15278,c_3831]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_23,plain,
% 3.77/0.98      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 3.77/0.98      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.77/0.98      | ~ v4_lattice3(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_185,plain,
% 3.77/0.98      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 3.77/0.98      | ~ v4_lattice3(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_23,c_14]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_470,plain,
% 3.77/0.98      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_185,c_29]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_471,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
% 3.77/0.98      | ~ l3_lattices(sK4)
% 3.77/0.98      | v2_struct_0(sK4)
% 3.77/0.98      | ~ v10_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_470]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_475,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_471,c_31,c_30,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2644,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_475]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3121,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2644]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_9,plain,
% 3.77/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.77/0.98      | r1_lattices(X0,X1,X3)
% 3.77/0.98      | ~ r2_hidden(X3,X2)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_830,plain,
% 3.77/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.77/0.98      | r1_lattices(X0,X1,X3)
% 3.77/0.98      | ~ r2_hidden(X3,X2)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_831,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | r1_lattices(sK4,X0,X2)
% 3.77/0.98      | ~ r2_hidden(X2,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_830]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_835,plain,
% 3.77/0.98      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ r2_hidden(X2,X1)
% 3.77/0.98      | r1_lattices(sK4,X0,X2)
% 3.77/0.98      | ~ r3_lattice3(sK4,X0,X1) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_831,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_836,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | r1_lattices(sK4,X0,X2)
% 3.77/0.98      | ~ r2_hidden(X2,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_835]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2630,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 3.77/0.98      | r1_lattices(sK4,X0_53,X1_53)
% 3.77/0.98      | ~ r2_hidden(X1_53,X0_54)
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_836]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3134,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,X0_54) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,X0_53,X1_53) = iProver_top
% 3.77/0.98      | r2_hidden(X1_53,X0_54) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.77/0.98      | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2630]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4537,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X1_54) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,X1_54) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3129,c_3134]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6700,plain,
% 3.77/0.98      ( r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,X0_54) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3121,c_4537]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3706,plain,
% 3.77/0.98      ( r1_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3129,c_3127]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6722,plain,
% 3.77/0.98      ( r3_lattices(sK4,k16_lattice3(sK4,X0_54),X0_53) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,X0_54) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_6700,c_3706]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_25,negated_conjecture,
% 3.77/0.98      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.77/0.98      | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
% 3.77/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2649,negated_conjecture,
% 3.77/0.98      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.77/0.98      | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3116,plain,
% 3.77/0.98      ( r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2649]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_16793,plain,
% 3.77/0.98      ( r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) != iProver_top
% 3.77/0.98      | r2_hidden(sK5,sK6) != iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_6722,c_3116]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_26,negated_conjecture,
% 3.77/0.98      ( r2_hidden(sK5,sK6) ),
% 3.77/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_37,plain,
% 3.77/0.98      ( r2_hidden(sK5,sK6) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_38,plain,
% 3.77/0.98      ( r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2676,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2644]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2678,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6) = iProver_top ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2676]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2701,plain,
% 3.77/0.98      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2703,plain,
% 3.77/0.98      ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2701]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3334,plain,
% 3.77/0.98      ( ~ r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.77/0.98      | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.77/0.98      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2637]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3335,plain,
% 3.77/0.98      ( r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
% 3.77/0.98      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_3334]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3410,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),X0_54)
% 3.77/0.98      | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.77/0.98      | ~ r2_hidden(sK5,X0_54)
% 3.77/0.98      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2630]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3414,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),X0_54) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
% 3.77/0.98      | r2_hidden(sK5,X0_54) != iProver_top
% 3.77/0.98      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_3410]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3416,plain,
% 3.77/0.98      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
% 3.77/0.98      | r2_hidden(sK5,sK6) != iProver_top
% 3.77/0.98      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_3414]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_16803,plain,
% 3.77/0.98      ( r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) != iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_16793,c_36,c_37,c_38,c_2678,c_2703,c_3335,c_3416]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_16808,plain,
% 3.77/0.98      ( sK2(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),sK4,sK6) = sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_15285,c_16803]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_18,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.77/0.98      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.77/0.98      | ~ v4_lattice3(X1)
% 3.77/0.98      | ~ l3_lattices(X1)
% 3.77/0.98      | v2_struct_0(X1)
% 3.77/0.98      | ~ v10_lattices(X1) ),
% 3.77/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_434,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.77/0.98      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.77/0.98      | ~ l3_lattices(X1)
% 3.77/0.98      | v2_struct_0(X1)
% 3.77/0.98      | ~ v10_lattices(X1)
% 3.77/0.98      | sK4 != X1 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_435,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.77/0.98      | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4)
% 3.77/0.98      | v2_struct_0(sK4)
% 3.77/0.98      | ~ v10_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_434]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_439,plain,
% 3.77/0.98      ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
% 3.77/0.98      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_435,c_31,c_30,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_440,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.77/0.98      | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_439]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2646,plain,
% 3.77/0.98      ( ~ r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | m1_subset_1(sK2(X0_53,sK4,X0_54),u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_440]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3119,plain,
% 3.77/0.98      ( r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | m1_subset_1(sK2(X0_53,sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2646]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_16901,plain,
% 3.77/0.98      ( r2_hidden(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top
% 3.77/0.98      | m1_subset_1(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_16808,c_3119]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2651,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2666,plain,
% 3.77/0.98      ( sK5 = sK5 ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2651]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2679,plain,
% 3.77/0.98      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6)) = k15_lattice3(sK4,sK6) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2643]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3746,plain,
% 3.77/0.98      ( k15_lattice3(sK4,sK6) = k15_lattice3(sK4,sK6) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2651]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2652,plain,
% 3.77/0.98      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 3.77/0.98      theory(equality) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3454,plain,
% 3.77/0.98      ( X0_53 != X1_53
% 3.77/0.98      | X0_53 = k16_lattice3(sK4,X0_54)
% 3.77/0.98      | k16_lattice3(sK4,X0_54) != X1_53 ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2652]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3646,plain,
% 3.77/0.98      ( X0_53 != k15_lattice3(sK4,X0_54)
% 3.77/0.98      | X0_53 = k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54)) != k15_lattice3(sK4,X0_54) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_3454]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3793,plain,
% 3.77/0.98      ( k15_lattice3(sK4,X0_54) != k15_lattice3(sK4,X0_54)
% 3.77/0.98      | k15_lattice3(sK4,X0_54) = k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54)) != k15_lattice3(sK4,X0_54) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_3646]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3795,plain,
% 3.77/0.98      ( k15_lattice3(sK4,sK6) != k15_lattice3(sK4,sK6)
% 3.77/0.98      | k15_lattice3(sK4,sK6) = k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))
% 3.77/0.98      | k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6)) != k15_lattice3(sK4,sK6) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_3793]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2653,plain,
% 3.77/0.98      ( ~ r3_lattices(X0_52,X0_53,X1_53)
% 3.77/0.98      | r3_lattices(X0_52,X2_53,X3_53)
% 3.77/0.98      | X2_53 != X0_53
% 3.77/0.98      | X3_53 != X1_53 ),
% 3.77/0.98      theory(equality) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3528,plain,
% 3.77/0.98      ( ~ r3_lattices(sK4,X0_53,X1_53)
% 3.77/0.98      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 3.77/0.98      | k15_lattice3(sK4,sK6) != X1_53
% 3.77/0.98      | sK5 != X0_53 ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2653]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4458,plain,
% 3.77/0.98      ( ~ r3_lattices(sK4,X0_53,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6)))
% 3.77/0.98      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 3.77/0.98      | k15_lattice3(sK4,sK6) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))
% 3.77/0.98      | sK5 != X0_53 ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_3528]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4459,plain,
% 3.77/0.98      ( k15_lattice3(sK4,sK6) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))
% 3.77/0.98      | sK5 != X0_53
% 3.77/0.98      | r3_lattices(sK4,X0_53,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_4458]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4461,plain,
% 3.77/0.98      ( k15_lattice3(sK4,sK6) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))
% 3.77/0.98      | sK5 != sK5
% 3.77/0.98      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) = iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))) != iProver_top ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_4459]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4839,plain,
% 3.77/0.98      ( ~ r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,sK6))
% 3.77/0.98      | r3_lattices(sK4,X0_53,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6)))
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2626]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4840,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,sK6)) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,X0_53,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_4839]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4842,plain,
% 3.77/0.98      ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,sK6)) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,k16_lattice3(sK4,a_2_2_lattice3(sK4,sK6))) = iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_4840]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8,plain,
% 3.77/0.98      ( r3_lattice3(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_857,plain,
% 3.77/0.98      ( r3_lattice3(X0,X1,X2)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_31]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_858,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_857]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_862,plain,
% 3.77/0.98      ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | r3_lattice3(sK4,X0,X1) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_858,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_863,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_862]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2629,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,X0_54)
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.77/0.98      | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_863]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6150,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,sK6))
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.77/0.98      | m1_subset_1(sK0(sK4,X0_53,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2629]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6156,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,sK6)) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.77/0.98      | m1_subset_1(sK0(sK4,X0_53,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_6150]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6158,plain,
% 3.77/0.98      ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,sK6)) = iProver_top
% 3.77/0.98      | m1_subset_1(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_6156]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_17268,plain,
% 3.77/0.98      ( m1_subset_1(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_16901,c_36,c_37,c_38,c_2666,c_2678,c_2679,c_2703,
% 3.77/0.98                 c_3335,c_3416,c_3746,c_3795,c_4461,c_4842,c_6158]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_17277,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6))) = iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6))) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_17268,c_3951]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3914,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | r2_hidden(sK0(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)),a_2_2_lattice3(sK4,X0_54))
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_2628]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3919,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | r2_hidden(sK0(sK4,X0_53,a_2_2_lattice3(sK4,X0_54)),a_2_2_lattice3(sK4,X0_54)) = iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_3914]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3921,plain,
% 3.77/0.98      ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,sK6)) = iProver_top
% 3.77/0.98      | r2_hidden(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) = iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_3919]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_16,plain,
% 3.77/0.98      ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.77/0.98      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.77/0.98      | ~ v4_lattice3(X0)
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_592,plain,
% 3.77/0.98      ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.77/0.98      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0)
% 3.77/0.98      | ~ v10_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_593,plain,
% 3.77/0.98      ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
% 3.77/0.98      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.77/0.98      | ~ l3_lattices(sK4)
% 3.77/0.98      | v2_struct_0(sK4)
% 3.77/0.98      | ~ v10_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_592]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_597,plain,
% 3.77/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.77/0.98      | r4_lattice3(sK4,sK2(X0,sK4,X1),X1) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_593,c_31,c_30,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_598,plain,
% 3.77/0.98      ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
% 3.77/0.98      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_597]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2639,plain,
% 3.77/0.98      ( r4_lattice3(sK4,sK2(X0_53,sK4,X0_54),X0_54)
% 3.77/0.98      | ~ r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_598]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3125,plain,
% 3.77/0.98      ( r4_lattice3(sK4,sK2(X0_53,sK4,X0_54),X0_54) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2639]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_13,plain,
% 3.77/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.77/0.98      | r1_lattices(X0,X3,X1)
% 3.77/0.98      | ~ r2_hidden(X3,X2)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_740,plain,
% 3.77/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.77/0.98      | r1_lattices(X0,X3,X1)
% 3.77/0.98      | ~ r2_hidden(X3,X2)
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_741,plain,
% 3.77/0.98      ( ~ r4_lattice3(sK4,X0,X1)
% 3.77/0.98      | r1_lattices(sK4,X2,X0)
% 3.77/0.98      | ~ r2_hidden(X2,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_740]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_745,plain,
% 3.77/0.98      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ r2_hidden(X2,X1)
% 3.77/0.98      | r1_lattices(sK4,X2,X0)
% 3.77/0.98      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_741,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_746,plain,
% 3.77/0.98      ( ~ r4_lattice3(sK4,X0,X1)
% 3.77/0.98      | r1_lattices(sK4,X2,X0)
% 3.77/0.98      | ~ r2_hidden(X2,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_745]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2634,plain,
% 3.77/0.98      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 3.77/0.98      | r1_lattices(sK4,X1_53,X0_53)
% 3.77/0.98      | ~ r2_hidden(X1_53,X0_54)
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 3.77/0.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_746]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3130,plain,
% 3.77/0.98      ( r4_lattice3(sK4,X0_53,X0_54) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,X1_53,X0_53) = iProver_top
% 3.77/0.98      | r2_hidden(X1_53,X0_54) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.77/0.98      | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2634]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4304,plain,
% 3.77/0.98      ( r4_lattice3(sK4,sK2(X0_53,sK4,X0_54),X1_54) != iProver_top
% 3.77/0.98      | r1_lattices(sK4,X1_53,sK2(X0_53,sK4,X0_54)) = iProver_top
% 3.77/0.98      | r2_hidden(X1_53,X1_54) != iProver_top
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3119,c_3130]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8439,plain,
% 3.77/0.98      ( r1_lattices(sK4,X0_53,sK2(X1_53,sK4,X0_54)) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,X0_54) != iProver_top
% 3.77/0.98      | r2_hidden(X1_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3125,c_4304]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3830,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3119,c_3705]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_9044,plain,
% 3.77/0.98      ( r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | r2_hidden(sK5,X0_54) != iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_8439,c_3830]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_11477,plain,
% 3.77/0.98      ( r2_hidden(sK5,X0_54) != iProver_top
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_9044,c_36]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_11478,plain,
% 3.77/0.98      ( r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | r2_hidden(sK5,X0_54) != iProver_top ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_11477]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3997,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
% 3.77/0.98      | r3_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) != iProver_top
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_3119,c_3951]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_11486,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,sK2(X0_53,sK4,X0_54)) = iProver_top
% 3.77/0.98      | r2_hidden(X0_53,a_2_2_lattice3(sK4,X0_54)) != iProver_top
% 3.77/0.98      | r2_hidden(sK5,X0_54) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_11478,c_3997]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_16886,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6))) = iProver_top
% 3.77/0.98      | r2_hidden(sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top
% 3.77/0.98      | r2_hidden(sK5,sK6) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_16808,c_11486]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_17350,plain,
% 3.77/0.98      ( r1_lattices(sK4,sK5,sK0(sK4,sK5,a_2_2_lattice3(sK4,sK6))) = iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_17277,c_36,c_37,c_38,c_2666,c_2678,c_2679,c_2703,
% 3.77/0.98                 c_3335,c_3416,c_3746,c_3795,c_3921,c_4461,c_4842,
% 3.77/0.98                 c_16886]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6,plain,
% 3.77/0.98      ( r3_lattice3(X0,X1,X2)
% 3.77/0.98      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | v2_struct_0(X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_899,plain,
% 3.77/0.98      ( r3_lattice3(X0,X1,X2)
% 3.77/0.98      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.77/0.98      | ~ l3_lattices(X0)
% 3.77/0.98      | sK4 != X0 ),
% 3.77/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_31]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_900,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ l3_lattices(sK4) ),
% 3.77/0.98      inference(unflattening,[status(thm)],[c_899]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_904,plain,
% 3.77/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.77/0.98      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.77/0.98      | r3_lattice3(sK4,X0,X1) ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_900,c_28]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_905,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.77/0.98      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_904]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2627,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,X0_54)
% 3.77/0.98      | ~ r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54))
% 3.77/0.98      | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
% 3.77/0.98      inference(subtyping,[status(esa)],[c_905]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3137,plain,
% 3.77/0.98      ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
% 3.77/0.98      | r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54)) != iProver_top
% 3.77/0.98      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2627]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_17355,plain,
% 3.77/0.98      ( r3_lattice3(sK4,sK5,a_2_2_lattice3(sK4,sK6)) = iProver_top
% 3.77/0.98      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_17350,c_3137]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(contradiction,plain,
% 3.77/0.98      ( $false ),
% 3.77/0.98      inference(minisat,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_17355,c_4842,c_4461,c_3795,c_3746,c_3416,c_3335,
% 3.77/0.98                 c_2703,c_2679,c_2678,c_2666,c_38,c_37,c_36]) ).
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  ------                               Statistics
% 3.77/0.98  
% 3.77/0.98  ------ General
% 3.77/0.98  
% 3.77/0.98  abstr_ref_over_cycles:                  0
% 3.77/0.98  abstr_ref_under_cycles:                 0
% 3.77/0.98  gc_basic_clause_elim:                   0
% 3.77/0.98  forced_gc_time:                         0
% 3.77/0.98  parsing_time:                           0.01
% 3.77/0.98  unif_index_cands_time:                  0.
% 3.77/0.98  unif_index_add_time:                    0.
% 3.77/0.98  orderings_time:                         0.
% 3.77/0.98  out_proof_time:                         0.015
% 3.77/0.98  total_time:                             0.477
% 3.77/0.98  num_of_symbols:                         56
% 3.77/0.98  num_of_terms:                           13154
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing
% 3.77/0.98  
% 3.77/0.98  num_of_splits:                          0
% 3.77/0.98  num_of_split_atoms:                     0
% 3.77/0.98  num_of_reused_defs:                     0
% 3.77/0.98  num_eq_ax_congr_red:                    60
% 3.77/0.98  num_of_sem_filtered_clauses:            1
% 3.77/0.98  num_of_subtypes:                        4
% 3.77/0.98  monotx_restored_types:                  1
% 3.77/0.98  sat_num_of_epr_types:                   0
% 3.77/0.98  sat_num_of_non_cyclic_types:            0
% 3.77/0.98  sat_guarded_non_collapsed_types:        1
% 3.77/0.98  num_pure_diseq_elim:                    0
% 3.77/0.98  simp_replaced_by:                       0
% 3.77/0.98  res_preprocessed:                       120
% 3.77/0.98  prep_upred:                             0
% 3.77/0.98  prep_unflattend:                        123
% 3.77/0.98  smt_new_axioms:                         0
% 3.77/0.98  pred_elim_cands:                        6
% 3.77/0.98  pred_elim:                              7
% 3.77/0.98  pred_elim_cl:                           7
% 3.77/0.98  pred_elim_cycles:                       13
% 3.77/0.98  merged_defs:                            0
% 3.77/0.98  merged_defs_ncl:                        0
% 3.77/0.98  bin_hyper_res:                          0
% 3.77/0.98  prep_cycles:                            4
% 3.77/0.98  pred_elim_time:                         0.037
% 3.77/0.98  splitting_time:                         0.
% 3.77/0.98  sem_filter_time:                        0.
% 3.77/0.98  monotx_time:                            0.001
% 3.77/0.98  subtype_inf_time:                       0.001
% 3.77/0.98  
% 3.77/0.98  ------ Problem properties
% 3.77/0.98  
% 3.77/0.98  clauses:                                24
% 3.77/0.98  conjectures:                            3
% 3.77/0.98  epr:                                    1
% 3.77/0.98  horn:                                   18
% 3.77/0.98  ground:                                 3
% 3.77/0.98  unary:                                  5
% 3.77/0.98  binary:                                 4
% 3.77/0.98  lits:                                   67
% 3.77/0.98  lits_eq:                                5
% 3.77/0.98  fd_pure:                                0
% 3.77/0.98  fd_pseudo:                              0
% 3.77/0.98  fd_cond:                                0
% 3.77/0.98  fd_pseudo_cond:                         3
% 3.77/0.98  ac_symbols:                             0
% 3.77/0.98  
% 3.77/0.98  ------ Propositional Solver
% 3.77/0.98  
% 3.77/0.98  prop_solver_calls:                      32
% 3.77/0.98  prop_fast_solver_calls:                 2148
% 3.77/0.98  smt_solver_calls:                       0
% 3.77/0.98  smt_fast_solver_calls:                  0
% 3.77/0.98  prop_num_of_clauses:                    5477
% 3.77/0.98  prop_preprocess_simplified:             11882
% 3.77/0.98  prop_fo_subsumed:                       124
% 3.77/0.98  prop_solver_time:                       0.
% 3.77/0.98  smt_solver_time:                        0.
% 3.77/0.98  smt_fast_solver_time:                   0.
% 3.77/0.98  prop_fast_solver_time:                  0.
% 3.77/0.98  prop_unsat_core_time:                   0.
% 3.77/0.98  
% 3.77/0.98  ------ QBF
% 3.77/0.98  
% 3.77/0.98  qbf_q_res:                              0
% 3.77/0.98  qbf_num_tautologies:                    0
% 3.77/0.98  qbf_prep_cycles:                        0
% 3.77/0.98  
% 3.77/0.98  ------ BMC1
% 3.77/0.98  
% 3.77/0.98  bmc1_current_bound:                     -1
% 3.77/0.98  bmc1_last_solved_bound:                 -1
% 3.77/0.98  bmc1_unsat_core_size:                   -1
% 3.77/0.98  bmc1_unsat_core_parents_size:           -1
% 3.77/0.98  bmc1_merge_next_fun:                    0
% 3.77/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.77/0.98  
% 3.77/0.98  ------ Instantiation
% 3.77/0.98  
% 3.77/0.98  inst_num_of_clauses:                    1262
% 3.77/0.98  inst_num_in_passive:                    393
% 3.77/0.98  inst_num_in_active:                     744
% 3.77/0.98  inst_num_in_unprocessed:                126
% 3.77/0.98  inst_num_of_loops:                      910
% 3.77/0.98  inst_num_of_learning_restarts:          0
% 3.77/0.98  inst_num_moves_active_passive:          161
% 3.77/0.98  inst_lit_activity:                      0
% 3.77/0.98  inst_lit_activity_moves:                0
% 3.77/0.98  inst_num_tautologies:                   0
% 3.77/0.98  inst_num_prop_implied:                  0
% 3.77/0.98  inst_num_existing_simplified:           0
% 3.77/0.98  inst_num_eq_res_simplified:             0
% 3.77/0.98  inst_num_child_elim:                    0
% 3.77/0.98  inst_num_of_dismatching_blockings:      1297
% 3.77/0.98  inst_num_of_non_proper_insts:           2296
% 3.77/0.98  inst_num_of_duplicates:                 0
% 3.77/0.98  inst_inst_num_from_inst_to_res:         0
% 3.77/0.98  inst_dismatching_checking_time:         0.
% 3.77/0.98  
% 3.77/0.98  ------ Resolution
% 3.77/0.98  
% 3.77/0.98  res_num_of_clauses:                     0
% 3.77/0.98  res_num_in_passive:                     0
% 3.77/0.98  res_num_in_active:                      0
% 3.77/0.98  res_num_of_loops:                       124
% 3.77/0.98  res_forward_subset_subsumed:            177
% 3.77/0.98  res_backward_subset_subsumed:           4
% 3.77/0.98  res_forward_subsumed:                   0
% 3.77/0.98  res_backward_subsumed:                  0
% 3.77/0.98  res_forward_subsumption_resolution:     6
% 3.77/0.98  res_backward_subsumption_resolution:    1
% 3.77/0.98  res_clause_to_clause_subsumption:       1879
% 3.77/0.98  res_orphan_elimination:                 0
% 3.77/0.98  res_tautology_del:                      233
% 3.77/0.98  res_num_eq_res_simplified:              0
% 3.77/0.98  res_num_sel_changes:                    0
% 3.77/0.98  res_moves_from_active_to_pass:          0
% 3.77/0.98  
% 3.77/0.98  ------ Superposition
% 3.77/0.98  
% 3.77/0.98  sup_time_total:                         0.
% 3.77/0.98  sup_time_generating:                    0.
% 3.77/0.98  sup_time_sim_full:                      0.
% 3.77/0.98  sup_time_sim_immed:                     0.
% 3.77/0.98  
% 3.77/0.98  sup_num_of_clauses:                     319
% 3.77/0.98  sup_num_in_active:                      181
% 3.77/0.98  sup_num_in_passive:                     138
% 3.77/0.98  sup_num_of_loops:                       181
% 3.77/0.98  sup_fw_superposition:                   215
% 3.77/0.98  sup_bw_superposition:                   149
% 3.77/0.98  sup_immediate_simplified:               61
% 3.77/0.98  sup_given_eliminated:                   0
% 3.77/0.98  comparisons_done:                       0
% 3.77/0.98  comparisons_avoided:                    2
% 3.77/0.98  
% 3.77/0.98  ------ Simplifications
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  sim_fw_subset_subsumed:                 7
% 3.77/0.98  sim_bw_subset_subsumed:                 10
% 3.77/0.98  sim_fw_subsumed:                        2
% 3.77/0.98  sim_bw_subsumed:                        2
% 3.77/0.98  sim_fw_subsumption_res:                 0
% 3.77/0.98  sim_bw_subsumption_res:                 0
% 3.77/0.98  sim_tautology_del:                      3
% 3.77/0.98  sim_eq_tautology_del:                   23
% 3.77/0.98  sim_eq_res_simp:                        0
% 3.77/0.98  sim_fw_demodulated:                     7
% 3.77/0.98  sim_bw_demodulated:                     0
% 3.77/0.98  sim_light_normalised:                   46
% 3.77/0.98  sim_joinable_taut:                      0
% 3.77/0.98  sim_joinable_simp:                      0
% 3.77/0.98  sim_ac_normalised:                      0
% 3.77/0.98  sim_smt_subsumption:                    0
% 3.77/0.98  
%------------------------------------------------------------------------------

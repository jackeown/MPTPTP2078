%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:14 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 623 expanded)
%              Number of clauses        :  119 ( 169 expanded)
%              Number of leaves         :   17 ( 190 expanded)
%              Depth                    :   21
%              Number of atoms          :  891 (4223 expanded)
%              Number of equality atoms :  130 ( 629 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k16_lattice3(X0,X2) != X1
          & r3_lattice3(X0,X1,X2)
          & r2_hidden(X1,X2) )
     => ( k16_lattice3(X0,sK6) != X1
        & r3_lattice3(X0,X1,sK6)
        & r2_hidden(X1,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k16_lattice3(X0,X2) != sK5
            & r3_lattice3(X0,sK5,X2)
            & r2_hidden(sK5,X2) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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
              ( k16_lattice3(sK4,X2) != X1
              & r3_lattice3(sK4,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k16_lattice3(sK4,sK6) != sK5
    & r3_lattice3(sK4,sK5,sK6)
    & r2_hidden(sK5,sK6)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f39,f38,f37])).

fof(f61,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f8,plain,(
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

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    r3_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f64,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_367,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_368,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_25,c_24,c_22])).

cnf(c_373,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_2535,plain,
    ( ~ r4_lattice3(sK4,X0_48,X0_49)
    | ~ r1_lattices(sK4,X0_48,sK2(sK4,X0_49,X0_48))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_49) = X0_48 ),
    inference(subtyping,[status(esa)],[c_373])).

cnf(c_14727,plain,
    ( ~ r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
    | ~ r1_lattices(sK4,X0_48,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) = X0_48 ),
    inference(instantiation,[status(thm)],[c_2535])).

cnf(c_14729,plain,
    ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | ~ r1_lattices(sK4,sK5,sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_14727])).

cnf(c_7,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_464,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_465,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_25])).

cnf(c_470,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_2531,plain,
    ( ~ r4_lattice3(sK4,X0_48,X0_49)
    | r1_lattices(sK4,X1_48,X0_48)
    | ~ r2_hidden(X1_48,X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_470])).

cnf(c_6540,plain,
    ( ~ r4_lattice3(sK4,sK2(sK4,X0_49,X0_48),X1_49)
    | r1_lattices(sK4,X1_48,sK2(sK4,X0_49,X0_48))
    | ~ r2_hidden(X1_48,X1_49)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,X0_49,X0_48),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_8842,plain,
    ( ~ r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),X1_49)
    | r1_lattices(sK4,X1_48,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48))
    | ~ r2_hidden(X1_48,X1_49)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6540])).

cnf(c_11860,plain,
    ( ~ r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),a_2_1_lattice3(sK4,X0_49))
    | r1_lattices(sK4,X1_48,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48))
    | ~ r2_hidden(X1_48,a_2_1_lattice3(sK4,X0_49))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8842])).

cnf(c_11862,plain,
    ( ~ r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5),a_2_1_lattice3(sK4,sK6))
    | r1_lattices(sK4,sK5,sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5))
    | ~ r2_hidden(sK5,a_2_1_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11860])).

cnf(c_2546,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_2545,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_3532,plain,
    ( X0_48 != X1_48
    | X1_48 = X0_48 ),
    inference(resolution,[status(thm)],[c_2546,c_2545])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_662,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | sK3(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_663,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | v2_struct_0(sK4)
    | sK3(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_667,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | sK3(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_663,c_25])).

cnf(c_2522,plain,
    ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
    | sK3(X0_48,sK4,X0_49) = X0_48 ),
    inference(subtyping,[status(esa)],[c_667])).

cnf(c_4345,plain,
    ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
    | X0_48 = sK3(X0_48,sK4,X0_49) ),
    inference(resolution,[status(thm)],[c_3532,c_2522])).

cnf(c_2547,plain,
    ( ~ r3_lattice3(X0_50,X0_48,X0_49)
    | r3_lattice3(X0_50,X1_48,X0_49)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_4461,plain,
    ( r3_lattice3(X0_50,X0_48,X0_49)
    | ~ r3_lattice3(X0_50,sK3(X0_48,sK4,X1_49),X0_49)
    | ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X1_49)) ),
    inference(resolution,[status(thm)],[c_4345,c_2547])).

cnf(c_15,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_414,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_415,plain,
    ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_419,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | r3_lattice3(sK4,sK3(X0,sK4,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_25])).

cnf(c_420,plain,
    ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_2534,plain,
    ( r3_lattice3(sK4,sK3(X0_48,sK4,X0_49),X0_49)
    | ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49)) ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_6343,plain,
    ( r3_lattice3(sK4,X0_48,X0_49)
    | ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49)) ),
    inference(resolution,[status(thm)],[c_4461,c_2534])).

cnf(c_5,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_512,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_513,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_25])).

cnf(c_518,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_517])).

cnf(c_2529,plain,
    ( r4_lattice3(sK4,X0_48,X0_49)
    | r2_hidden(sK1(sK4,X0_48,X0_49),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_518])).

cnf(c_6518,plain,
    ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
    | r3_lattice3(sK4,sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_6343,c_2529])).

cnf(c_3,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_554,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_555,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattice3(sK4,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X2)
    | ~ r3_lattice3(sK4,X0,X2)
    | r1_lattices(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_25])).

cnf(c_560,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattice3(sK4,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_2527,plain,
    ( r1_lattices(sK4,X0_48,X1_48)
    | ~ r3_lattice3(sK4,X0_48,X0_49)
    | ~ r2_hidden(X1_48,X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_560])).

cnf(c_6655,plain,
    ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
    | r1_lattices(sK4,sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),X1_48)
    | ~ r2_hidden(X1_48,X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_6518,c_2527])).

cnf(c_2549,plain,
    ( ~ m1_subset_1(X0_48,X0_51)
    | m1_subset_1(X1_48,X0_51)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_4459,plain,
    ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
    | m1_subset_1(X0_48,X0_51)
    | ~ m1_subset_1(sK3(X0_48,sK4,X0_49),X0_51) ),
    inference(resolution,[status(thm)],[c_4345,c_2549])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_644,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_645,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | m1_subset_1(sK3(X0,sK4,X1),u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_649,plain,
    ( m1_subset_1(sK3(X0,sK4,X1),u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_25])).

cnf(c_650,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | m1_subset_1(sK3(X0,sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_649])).

cnf(c_2523,plain,
    ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
    | m1_subset_1(sK3(X0_48,sK4,X0_49),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_650])).

cnf(c_6259,plain,
    ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
    | m1_subset_1(X0_48,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_4459,c_2523])).

cnf(c_6358,plain,
    ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_6259,c_2529])).

cnf(c_8206,plain,
    ( ~ m1_subset_1(X1_48,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | ~ r2_hidden(X1_48,X0_49)
    | r1_lattices(sK4,sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),X1_48)
    | r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6655,c_6358])).

cnf(c_8207,plain,
    ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
    | r1_lattices(sK4,sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),X1_48)
    | ~ r2_hidden(X1_48,X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_8206])).

cnf(c_4,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_533,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_534,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_25])).

cnf(c_539,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_2528,plain,
    ( r4_lattice3(sK4,X0_48,X0_49)
    | ~ r1_lattices(sK4,sK1(sK4,X0_48,X0_49),X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_539])).

cnf(c_8240,plain,
    ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
    | ~ r2_hidden(X0_48,X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_8207,c_2528])).

cnf(c_8242,plain,
    ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8240])).

cnf(c_3709,plain,
    ( X0_48 != X1_48
    | X0_48 = k15_lattice3(sK4,X0_49)
    | k15_lattice3(sK4,X0_49) != X1_48 ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_7439,plain,
    ( X0_48 != X1_48
    | X0_48 = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) != X1_48 ),
    inference(instantiation,[status(thm)],[c_3709])).

cnf(c_7440,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
    | sK5 = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7439])).

cnf(c_9,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_343,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_344,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_25,c_24,c_22])).

cnf(c_349,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_348])).

cnf(c_2536,plain,
    ( ~ r4_lattice3(sK4,X0_48,X0_49)
    | r4_lattice3(sK4,sK2(sK4,X0_49,X0_48),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_49) = X0_48 ),
    inference(subtyping,[status(esa)],[c_349])).

cnf(c_5707,plain,
    ( ~ r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
    | r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),a_2_1_lattice3(sK4,X0_49))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) = X0_48 ),
    inference(instantiation,[status(thm)],[c_2536])).

cnf(c_5713,plain,
    ( r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5),a_2_1_lattice3(sK4,sK6))
    | ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_5707])).

cnf(c_10,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_319,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_320,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_324,plain,
    ( m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_25,c_24,c_22])).

cnf(c_325,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_2537,plain,
    ( ~ r4_lattice3(sK4,X0_48,X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0_49,X0_48),u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_49) = X0_48 ),
    inference(subtyping,[status(esa)],[c_325])).

cnf(c_5489,plain,
    ( ~ r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) = X0_48 ),
    inference(instantiation,[status(thm)],[c_2537])).

cnf(c_5491,plain,
    ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
    | m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_5489])).

cnf(c_3216,plain,
    ( k16_lattice3(sK4,sK6) != X0_48
    | k16_lattice3(sK4,sK6) = sK5
    | sK5 != X0_48 ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_3895,plain,
    ( k16_lattice3(sK4,sK6) != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
    | k16_lattice3(sK4,sK6) = sK5
    | sK5 != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_3216])).

cnf(c_3257,plain,
    ( X0_48 != X1_48
    | k16_lattice3(sK4,sK6) != X1_48
    | k16_lattice3(sK4,sK6) = X0_48 ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_3397,plain,
    ( X0_48 != k16_lattice3(sK4,sK6)
    | k16_lattice3(sK4,sK6) = X0_48
    | k16_lattice3(sK4,sK6) != k16_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_3257])).

cnf(c_3721,plain,
    ( k16_lattice3(sK4,sK6) != k16_lattice3(sK4,sK6)
    | k16_lattice3(sK4,sK6) = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != k16_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_3397])).

cnf(c_3256,plain,
    ( k16_lattice3(sK4,sK6) = k16_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_453,plain,
    ( v2_struct_0(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_454,plain,
    ( v2_struct_0(sK4)
    | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_458,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_25])).

cnf(c_2532,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) = k16_lattice3(sK4,X0_49) ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_2581,plain,
    ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = k16_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_18,negated_conjecture,
    ( k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2543,negated_conjecture,
    ( k16_lattice3(sK4,sK6) != sK5 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2558,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_19,negated_conjecture,
    ( r3_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_432,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_433,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_25])).

cnf(c_438,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_437])).

cnf(c_772,plain,
    ( r2_hidden(X0,a_2_1_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | sK5 != X0
    | sK6 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_438])).

cnf(c_773,plain,
    ( r2_hidden(sK5,a_2_1_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14729,c_11862,c_8242,c_7440,c_5713,c_5491,c_3895,c_3721,c_3256,c_2581,c_2543,c_2558,c_773,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:41:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.84/1.08  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.08  
% 3.84/1.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.08  
% 3.84/1.08  ------  iProver source info
% 3.84/1.08  
% 3.84/1.08  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.08  git: non_committed_changes: false
% 3.84/1.08  git: last_make_outside_of_git: false
% 3.84/1.08  
% 3.84/1.08  ------ 
% 3.84/1.08  ------ Parsing...
% 3.84/1.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.08  
% 3.84/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.84/1.08  
% 3.84/1.08  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.08  
% 3.84/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.08  ------ Proving...
% 3.84/1.08  ------ Problem Properties 
% 3.84/1.08  
% 3.84/1.08  
% 3.84/1.08  clauses                                 22
% 3.84/1.08  conjectures                             4
% 3.84/1.08  EPR                                     2
% 3.84/1.08  Horn                                    16
% 3.84/1.08  unary                                   5
% 3.84/1.08  binary                                  4
% 3.84/1.08  lits                                    60
% 3.84/1.08  lits eq                                 6
% 3.84/1.08  fd_pure                                 0
% 3.84/1.08  fd_pseudo                               0
% 3.84/1.08  fd_cond                                 0
% 3.84/1.08  fd_pseudo_cond                          3
% 3.84/1.08  AC symbols                              0
% 3.84/1.08  
% 3.84/1.08  ------ Input Options Time Limit: Unbounded
% 3.84/1.08  
% 3.84/1.08  
% 3.84/1.08  ------ 
% 3.84/1.08  Current options:
% 3.84/1.08  ------ 
% 3.84/1.08  
% 3.84/1.08  
% 3.84/1.08  
% 3.84/1.08  
% 3.84/1.08  ------ Proving...
% 3.84/1.08  
% 3.84/1.08  
% 3.84/1.08  % SZS status Theorem for theBenchmark.p
% 3.84/1.08  
% 3.84/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.08  
% 3.84/1.08  fof(f3,axiom,(
% 3.84/1.08    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 3.84/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.08  
% 3.84/1.08  fof(f12,plain,(
% 3.84/1.08    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.08    inference(ennf_transformation,[],[f3])).
% 3.84/1.08  
% 3.84/1.08  fof(f13,plain,(
% 3.84/1.08    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(flattening,[],[f12])).
% 3.84/1.08  
% 3.84/1.08  fof(f28,plain,(
% 3.84/1.08    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(nnf_transformation,[],[f13])).
% 3.84/1.08  
% 3.84/1.08  fof(f29,plain,(
% 3.84/1.08    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(flattening,[],[f28])).
% 3.84/1.08  
% 3.84/1.08  fof(f30,plain,(
% 3.84/1.08    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(rectify,[],[f29])).
% 3.84/1.08  
% 3.84/1.08  fof(f31,plain,(
% 3.84/1.08    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.84/1.08    introduced(choice_axiom,[])).
% 3.84/1.08  
% 3.84/1.08  fof(f32,plain,(
% 3.84/1.08    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 3.84/1.08  
% 3.84/1.08  fof(f53,plain,(
% 3.84/1.08    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK2(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f32])).
% 3.84/1.08  
% 3.84/1.08  fof(f6,conjecture,(
% 3.84/1.08    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 3.84/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.08  
% 3.84/1.08  fof(f7,negated_conjecture,(
% 3.84/1.08    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 3.84/1.08    inference(negated_conjecture,[],[f6])).
% 3.84/1.08  
% 3.84/1.08  fof(f18,plain,(
% 3.84/1.08    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.84/1.08    inference(ennf_transformation,[],[f7])).
% 3.84/1.08  
% 3.84/1.08  fof(f19,plain,(
% 3.84/1.08    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.84/1.08    inference(flattening,[],[f18])).
% 3.84/1.08  
% 3.84/1.08  fof(f39,plain,(
% 3.84/1.08    ( ! [X0,X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => (k16_lattice3(X0,sK6) != X1 & r3_lattice3(X0,X1,sK6) & r2_hidden(X1,sK6))) )),
% 3.84/1.08    introduced(choice_axiom,[])).
% 3.84/1.08  
% 3.84/1.08  fof(f38,plain,(
% 3.84/1.08    ( ! [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k16_lattice3(X0,X2) != sK5 & r3_lattice3(X0,sK5,X2) & r2_hidden(sK5,X2)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.84/1.08    introduced(choice_axiom,[])).
% 3.84/1.08  
% 3.84/1.08  fof(f37,plain,(
% 3.84/1.08    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK4,X2) != X1 & r3_lattice3(sK4,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 3.84/1.08    introduced(choice_axiom,[])).
% 3.84/1.08  
% 3.84/1.08  fof(f40,plain,(
% 3.84/1.08    ((k16_lattice3(sK4,sK6) != sK5 & r3_lattice3(sK4,sK5,sK6) & r2_hidden(sK5,sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 3.84/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f39,f38,f37])).
% 3.84/1.08  
% 3.84/1.08  fof(f61,plain,(
% 3.84/1.08    v4_lattice3(sK4)),
% 3.84/1.08    inference(cnf_transformation,[],[f40])).
% 3.84/1.08  
% 3.84/1.08  fof(f59,plain,(
% 3.84/1.08    ~v2_struct_0(sK4)),
% 3.84/1.08    inference(cnf_transformation,[],[f40])).
% 3.84/1.08  
% 3.84/1.08  fof(f60,plain,(
% 3.84/1.08    v10_lattices(sK4)),
% 3.84/1.08    inference(cnf_transformation,[],[f40])).
% 3.84/1.08  
% 3.84/1.08  fof(f62,plain,(
% 3.84/1.08    l3_lattices(sK4)),
% 3.84/1.08    inference(cnf_transformation,[],[f40])).
% 3.84/1.08  
% 3.84/1.08  fof(f2,axiom,(
% 3.84/1.08    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.84/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.08  
% 3.84/1.08  fof(f10,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.08    inference(ennf_transformation,[],[f2])).
% 3.84/1.08  
% 3.84/1.08  fof(f11,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(flattening,[],[f10])).
% 3.84/1.08  
% 3.84/1.08  fof(f24,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(nnf_transformation,[],[f11])).
% 3.84/1.08  
% 3.84/1.08  fof(f25,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(rectify,[],[f24])).
% 3.84/1.08  
% 3.84/1.08  fof(f26,plain,(
% 3.84/1.08    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.84/1.08    introduced(choice_axiom,[])).
% 3.84/1.08  
% 3.84/1.08  fof(f27,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 3.84/1.08  
% 3.84/1.08  fof(f45,plain,(
% 3.84/1.08    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f27])).
% 3.84/1.08  
% 3.84/1.08  fof(f5,axiom,(
% 3.84/1.08    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.84/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.08  
% 3.84/1.08  fof(f16,plain,(
% 3.84/1.08    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 3.84/1.08    inference(ennf_transformation,[],[f5])).
% 3.84/1.08  
% 3.84/1.08  fof(f17,plain,(
% 3.84/1.08    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.84/1.08    inference(flattening,[],[f16])).
% 3.84/1.08  
% 3.84/1.08  fof(f33,plain,(
% 3.84/1.08    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.84/1.08    inference(nnf_transformation,[],[f17])).
% 3.84/1.08  
% 3.84/1.08  fof(f34,plain,(
% 3.84/1.08    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.84/1.08    inference(rectify,[],[f33])).
% 3.84/1.08  
% 3.84/1.08  fof(f35,plain,(
% 3.84/1.08    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 3.84/1.08    introduced(choice_axiom,[])).
% 3.84/1.08  
% 3.84/1.08  fof(f36,plain,(
% 3.84/1.08    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.84/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 3.84/1.08  
% 3.84/1.08  fof(f56,plain,(
% 3.84/1.08    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f36])).
% 3.84/1.08  
% 3.84/1.08  fof(f57,plain,(
% 3.84/1.08    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK3(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f36])).
% 3.84/1.08  
% 3.84/1.08  fof(f47,plain,(
% 3.84/1.08    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f27])).
% 3.84/1.08  
% 3.84/1.08  fof(f1,axiom,(
% 3.84/1.08    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.84/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.08  
% 3.84/1.08  fof(f8,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.08    inference(ennf_transformation,[],[f1])).
% 3.84/1.08  
% 3.84/1.08  fof(f9,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(flattening,[],[f8])).
% 3.84/1.08  
% 3.84/1.08  fof(f20,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(nnf_transformation,[],[f9])).
% 3.84/1.08  
% 3.84/1.08  fof(f21,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(rectify,[],[f20])).
% 3.84/1.08  
% 3.84/1.08  fof(f22,plain,(
% 3.84/1.08    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.84/1.08    introduced(choice_axiom,[])).
% 3.84/1.08  
% 3.84/1.08  fof(f23,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.84/1.08  
% 3.84/1.08  fof(f41,plain,(
% 3.84/1.08    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f23])).
% 3.84/1.08  
% 3.84/1.08  fof(f55,plain,(
% 3.84/1.08    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f36])).
% 3.84/1.08  
% 3.84/1.08  fof(f48,plain,(
% 3.84/1.08    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f27])).
% 3.84/1.08  
% 3.84/1.08  fof(f52,plain,(
% 3.84/1.08    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK2(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f32])).
% 3.84/1.08  
% 3.84/1.08  fof(f51,plain,(
% 3.84/1.08    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f32])).
% 3.84/1.08  
% 3.84/1.08  fof(f4,axiom,(
% 3.84/1.08    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1))),
% 3.84/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.08  
% 3.84/1.08  fof(f14,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.08    inference(ennf_transformation,[],[f4])).
% 3.84/1.08  
% 3.84/1.08  fof(f15,plain,(
% 3.84/1.08    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.08    inference(flattening,[],[f14])).
% 3.84/1.08  
% 3.84/1.08  fof(f54,plain,(
% 3.84/1.08    ( ! [X0,X1] : (k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f15])).
% 3.84/1.08  
% 3.84/1.08  fof(f66,plain,(
% 3.84/1.08    k16_lattice3(sK4,sK6) != sK5),
% 3.84/1.08    inference(cnf_transformation,[],[f40])).
% 3.84/1.08  
% 3.84/1.08  fof(f65,plain,(
% 3.84/1.08    r3_lattice3(sK4,sK5,sK6)),
% 3.84/1.08    inference(cnf_transformation,[],[f40])).
% 3.84/1.08  
% 3.84/1.08  fof(f58,plain,(
% 3.84/1.08    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.08    inference(cnf_transformation,[],[f36])).
% 3.84/1.08  
% 3.84/1.08  fof(f69,plain,(
% 3.84/1.08    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.08    inference(equality_resolution,[],[f58])).
% 3.84/1.08  
% 3.84/1.08  fof(f64,plain,(
% 3.84/1.08    r2_hidden(sK5,sK6)),
% 3.84/1.08    inference(cnf_transformation,[],[f40])).
% 3.84/1.08  
% 3.84/1.08  fof(f63,plain,(
% 3.84/1.08    m1_subset_1(sK5,u1_struct_0(sK4))),
% 3.84/1.08    inference(cnf_transformation,[],[f40])).
% 3.84/1.08  
% 3.84/1.08  cnf(c_8,plain,
% 3.84/1.08      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.08      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | ~ v10_lattices(X0)
% 3.84/1.08      | ~ v4_lattice3(X0)
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0)
% 3.84/1.08      | k15_lattice3(X0,X2) = X1 ),
% 3.84/1.08      inference(cnf_transformation,[],[f53]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_23,negated_conjecture,
% 3.84/1.08      ( v4_lattice3(sK4) ),
% 3.84/1.08      inference(cnf_transformation,[],[f61]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_367,plain,
% 3.84/1.08      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.08      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | ~ v10_lattices(X0)
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0)
% 3.84/1.08      | k15_lattice3(X0,X2) = X1
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_368,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ v10_lattices(sK4)
% 3.84/1.08      | v2_struct_0(sK4)
% 3.84/1.08      | ~ l3_lattices(sK4)
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_367]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_25,negated_conjecture,
% 3.84/1.08      ( ~ v2_struct_0(sK4) ),
% 3.84/1.08      inference(cnf_transformation,[],[f59]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_24,negated_conjecture,
% 3.84/1.08      ( v10_lattices(sK4) ),
% 3.84/1.08      inference(cnf_transformation,[],[f60]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_22,negated_conjecture,
% 3.84/1.08      ( l3_lattices(sK4) ),
% 3.84/1.08      inference(cnf_transformation,[],[f62]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_372,plain,
% 3.84/1.08      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 3.84/1.08      | ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_368,c_25,c_24,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_373,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_372]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2535,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0_48,X0_49)
% 3.84/1.08      | ~ r1_lattices(sK4,X0_48,sK2(sK4,X0_49,X0_48))
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,X0_49) = X0_48 ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_373]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_14727,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | ~ r1_lattices(sK4,X0_48,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48))
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) = X0_48 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2535]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_14729,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | ~ r1_lattices(sK4,sK5,sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5))
% 3.84/1.08      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = sK5 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_14727]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_7,plain,
% 3.84/1.08      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.08      | r1_lattices(X0,X3,X1)
% 3.84/1.08      | ~ r2_hidden(X3,X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0) ),
% 3.84/1.08      inference(cnf_transformation,[],[f45]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_464,plain,
% 3.84/1.08      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.08      | r1_lattices(X0,X3,X1)
% 3.84/1.08      | ~ r2_hidden(X3,X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_465,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | r1_lattices(sK4,X2,X0)
% 3.84/1.08      | ~ r2_hidden(X2,X1)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.84/1.08      | v2_struct_0(sK4) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_464]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_469,plain,
% 3.84/1.08      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ r2_hidden(X2,X1)
% 3.84/1.08      | r1_lattices(sK4,X2,X0)
% 3.84/1.08      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_465,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_470,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | r1_lattices(sK4,X2,X0)
% 3.84/1.08      | ~ r2_hidden(X2,X1)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_469]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2531,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0_48,X0_49)
% 3.84/1.08      | r1_lattices(sK4,X1_48,X0_48)
% 3.84/1.08      | ~ r2_hidden(X1_48,X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X1_48,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_470]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_6540,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,sK2(sK4,X0_49,X0_48),X1_49)
% 3.84/1.08      | r1_lattices(sK4,X1_48,sK2(sK4,X0_49,X0_48))
% 3.84/1.08      | ~ r2_hidden(X1_48,X1_49)
% 3.84/1.08      | ~ m1_subset_1(X1_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(sK2(sK4,X0_49,X0_48),u1_struct_0(sK4)) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2531]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_8842,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),X1_49)
% 3.84/1.08      | r1_lattices(sK4,X1_48,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48))
% 3.84/1.08      | ~ r2_hidden(X1_48,X1_49)
% 3.84/1.08      | ~ m1_subset_1(X1_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),u1_struct_0(sK4)) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_6540]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_11860,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | r1_lattices(sK4,X1_48,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48))
% 3.84/1.08      | ~ r2_hidden(X1_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | ~ m1_subset_1(X1_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),u1_struct_0(sK4)) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_8842]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_11862,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5),a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | r1_lattices(sK4,sK5,sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5))
% 3.84/1.08      | ~ r2_hidden(sK5,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | ~ m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5),u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_11860]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2546,plain,
% 3.84/1.08      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 3.84/1.08      theory(equality) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2545,plain,( X0_48 = X0_48 ),theory(equality) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3532,plain,
% 3.84/1.08      ( X0_48 != X1_48 | X1_48 = X0_48 ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_2546,c_2545]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_16,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.84/1.08      | v2_struct_0(X1)
% 3.84/1.08      | ~ l3_lattices(X1)
% 3.84/1.08      | sK3(X0,X1,X2) = X0 ),
% 3.84/1.08      inference(cnf_transformation,[],[f56]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_662,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.84/1.08      | v2_struct_0(X1)
% 3.84/1.08      | sK3(X0,X1,X2) = X0
% 3.84/1.08      | sK4 != X1 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_663,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | v2_struct_0(sK4)
% 3.84/1.08      | sK3(X0,sK4,X1) = X0 ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_662]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_667,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) | sK3(X0,sK4,X1) = X0 ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_663,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2522,plain,
% 3.84/1.08      ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | sK3(X0_48,sK4,X0_49) = X0_48 ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_667]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_4345,plain,
% 3.84/1.08      ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | X0_48 = sK3(X0_48,sK4,X0_49) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_3532,c_2522]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2547,plain,
% 3.84/1.08      ( ~ r3_lattice3(X0_50,X0_48,X0_49)
% 3.84/1.08      | r3_lattice3(X0_50,X1_48,X0_49)
% 3.84/1.08      | X1_48 != X0_48 ),
% 3.84/1.08      theory(equality) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_4461,plain,
% 3.84/1.08      ( r3_lattice3(X0_50,X0_48,X0_49)
% 3.84/1.08      | ~ r3_lattice3(X0_50,sK3(X0_48,sK4,X1_49),X0_49)
% 3.84/1.08      | ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X1_49)) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_4345,c_2547]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_15,plain,
% 3.84/1.08      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 3.84/1.08      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0) ),
% 3.84/1.08      inference(cnf_transformation,[],[f57]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_414,plain,
% 3.84/1.08      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 3.84/1.08      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_415,plain,
% 3.84/1.08      ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
% 3.84/1.08      | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | v2_struct_0(sK4) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_414]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_419,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | r3_lattice3(sK4,sK3(X0,sK4,X1),X1) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_415,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_420,plain,
% 3.84/1.08      ( r3_lattice3(sK4,sK3(X0,sK4,X1),X1)
% 3.84/1.08      | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_419]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2534,plain,
% 3.84/1.08      ( r3_lattice3(sK4,sK3(X0_48,sK4,X0_49),X0_49)
% 3.84/1.08      | ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49)) ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_420]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_6343,plain,
% 3.84/1.08      ( r3_lattice3(sK4,X0_48,X0_49)
% 3.84/1.08      | ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49)) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_4461,c_2534]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_5,plain,
% 3.84/1.08      ( r4_lattice3(X0,X1,X2)
% 3.84/1.08      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0) ),
% 3.84/1.08      inference(cnf_transformation,[],[f47]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_512,plain,
% 3.84/1.08      ( r4_lattice3(X0,X1,X2)
% 3.84/1.08      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_513,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | v2_struct_0(sK4) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_512]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_517,plain,
% 3.84/1.08      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.84/1.08      | r4_lattice3(sK4,X0,X1) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_513,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_518,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_517]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2529,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0_48,X0_49)
% 3.84/1.08      | r2_hidden(sK1(sK4,X0_48,X0_49),X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_518]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_6518,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | r3_lattice3(sK4,sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_6343,c_2529]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3,plain,
% 3.84/1.08      ( r1_lattices(X0,X1,X2)
% 3.84/1.08      | ~ r3_lattice3(X0,X1,X3)
% 3.84/1.08      | ~ r2_hidden(X2,X3)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0) ),
% 3.84/1.08      inference(cnf_transformation,[],[f41]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_554,plain,
% 3.84/1.08      ( r1_lattices(X0,X1,X2)
% 3.84/1.08      | ~ r3_lattice3(X0,X1,X3)
% 3.84/1.08      | ~ r2_hidden(X2,X3)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_555,plain,
% 3.84/1.08      ( r1_lattices(sK4,X0,X1)
% 3.84/1.08      | ~ r3_lattice3(sK4,X0,X2)
% 3.84/1.08      | ~ r2_hidden(X1,X2)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.84/1.08      | v2_struct_0(sK4) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_554]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_559,plain,
% 3.84/1.08      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ r2_hidden(X1,X2)
% 3.84/1.08      | ~ r3_lattice3(sK4,X0,X2)
% 3.84/1.08      | r1_lattices(sK4,X0,X1) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_555,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_560,plain,
% 3.84/1.08      ( r1_lattices(sK4,X0,X1)
% 3.84/1.08      | ~ r3_lattice3(sK4,X0,X2)
% 3.84/1.08      | ~ r2_hidden(X1,X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_559]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2527,plain,
% 3.84/1.08      ( r1_lattices(sK4,X0_48,X1_48)
% 3.84/1.08      | ~ r3_lattice3(sK4,X0_48,X0_49)
% 3.84/1.08      | ~ r2_hidden(X1_48,X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X1_48,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_560]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_6655,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | r1_lattices(sK4,sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),X1_48)
% 3.84/1.08      | ~ r2_hidden(X1_48,X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X1_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),u1_struct_0(sK4)) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_6518,c_2527]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2549,plain,
% 3.84/1.08      ( ~ m1_subset_1(X0_48,X0_51)
% 3.84/1.08      | m1_subset_1(X1_48,X0_51)
% 3.84/1.08      | X1_48 != X0_48 ),
% 3.84/1.08      theory(equality) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_4459,plain,
% 3.84/1.08      ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | m1_subset_1(X0_48,X0_51)
% 3.84/1.08      | ~ m1_subset_1(sK3(X0_48,sK4,X0_49),X0_51) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_4345,c_2549]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_17,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.84/1.08      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 3.84/1.08      | v2_struct_0(X1)
% 3.84/1.08      | ~ l3_lattices(X1) ),
% 3.84/1.08      inference(cnf_transformation,[],[f55]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_644,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.84/1.08      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 3.84/1.08      | v2_struct_0(X1)
% 3.84/1.08      | sK4 != X1 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_645,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | m1_subset_1(sK3(X0,sK4,X1),u1_struct_0(sK4))
% 3.84/1.08      | v2_struct_0(sK4) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_644]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_649,plain,
% 3.84/1.08      ( m1_subset_1(sK3(X0,sK4,X1),u1_struct_0(sK4))
% 3.84/1.08      | ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1)) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_645,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_650,plain,
% 3.84/1.08      ( ~ r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | m1_subset_1(sK3(X0,sK4,X1),u1_struct_0(sK4)) ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_649]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2523,plain,
% 3.84/1.08      ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | m1_subset_1(sK3(X0_48,sK4,X0_49),u1_struct_0(sK4)) ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_650]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_6259,plain,
% 3.84/1.08      ( ~ r2_hidden(X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | m1_subset_1(X0_48,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_4459,c_2523]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_6358,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | m1_subset_1(sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),u1_struct_0(sK4)) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_6259,c_2529]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_8206,plain,
% 3.84/1.08      ( ~ m1_subset_1(X1_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ r2_hidden(X1_48,X0_49)
% 3.84/1.08      | r1_lattices(sK4,sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),X1_48)
% 3.84/1.08      | r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_6655,c_6358]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_8207,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | r1_lattices(sK4,sK1(sK4,X0_48,a_2_1_lattice3(sK4,X0_49)),X1_48)
% 3.84/1.08      | ~ r2_hidden(X1_48,X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X1_48,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_8206]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_4,plain,
% 3.84/1.08      ( r4_lattice3(X0,X1,X2)
% 3.84/1.08      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0) ),
% 3.84/1.08      inference(cnf_transformation,[],[f48]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_533,plain,
% 3.84/1.08      ( r4_lattice3(X0,X1,X2)
% 3.84/1.08      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_534,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | v2_struct_0(sK4) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_533]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_538,plain,
% 3.84/1.08      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.84/1.08      | r4_lattice3(sK4,X0,X1) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_534,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_539,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_538]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2528,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0_48,X0_49)
% 3.84/1.08      | ~ r1_lattices(sK4,sK1(sK4,X0_48,X0_49),X0_48)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_539]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_8240,plain,
% 3.84/1.08      ( r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | ~ r2_hidden(X0_48,X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(resolution,[status(thm)],[c_8207,c_2528]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_8242,plain,
% 3.84/1.08      ( r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | ~ r2_hidden(sK5,sK6)
% 3.84/1.08      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_8240]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3709,plain,
% 3.84/1.08      ( X0_48 != X1_48
% 3.84/1.08      | X0_48 = k15_lattice3(sK4,X0_49)
% 3.84/1.08      | k15_lattice3(sK4,X0_49) != X1_48 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2546]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_7439,plain,
% 3.84/1.08      ( X0_48 != X1_48
% 3.84/1.08      | X0_48 = k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) != X1_48 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_3709]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_7440,plain,
% 3.84/1.08      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != sK5
% 3.84/1.08      | sK5 = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | sK5 != sK5 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_7439]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_9,plain,
% 3.84/1.08      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.08      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | ~ v10_lattices(X0)
% 3.84/1.08      | ~ v4_lattice3(X0)
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0)
% 3.84/1.08      | k15_lattice3(X0,X2) = X1 ),
% 3.84/1.08      inference(cnf_transformation,[],[f52]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_343,plain,
% 3.84/1.08      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.08      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | ~ v10_lattices(X0)
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0)
% 3.84/1.08      | k15_lattice3(X0,X2) = X1
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_344,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ v10_lattices(sK4)
% 3.84/1.08      | v2_struct_0(sK4)
% 3.84/1.08      | ~ l3_lattices(sK4)
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_343]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_348,plain,
% 3.84/1.08      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 3.84/1.08      | ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_344,c_25,c_24,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_349,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_348]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2536,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0_48,X0_49)
% 3.84/1.08      | r4_lattice3(sK4,sK2(sK4,X0_49,X0_48),X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,X0_49) = X0_48 ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_349]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_5707,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) = X0_48 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2536]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_5713,plain,
% 3.84/1.08      ( r4_lattice3(sK4,sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5),a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = sK5 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_5707]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_10,plain,
% 3.84/1.08      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 3.84/1.08      | ~ v10_lattices(X0)
% 3.84/1.08      | ~ v4_lattice3(X0)
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0)
% 3.84/1.08      | k15_lattice3(X0,X2) = X1 ),
% 3.84/1.08      inference(cnf_transformation,[],[f51]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_319,plain,
% 3.84/1.08      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 3.84/1.08      | ~ v10_lattices(X0)
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0)
% 3.84/1.08      | k15_lattice3(X0,X2) = X1
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_320,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 3.84/1.08      | ~ v10_lattices(sK4)
% 3.84/1.08      | v2_struct_0(sK4)
% 3.84/1.08      | ~ l3_lattices(sK4)
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_319]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_324,plain,
% 3.84/1.08      ( m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_320,c_25,c_24,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_325,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0,X1)
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,X1) = X0 ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_324]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2537,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0_48,X0_49)
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | m1_subset_1(sK2(sK4,X0_49,X0_48),u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,X0_49) = X0_48 ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_325]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_5489,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,X0_48,a_2_1_lattice3(sK4,X0_49))
% 3.84/1.08      | ~ m1_subset_1(X0_48,u1_struct_0(sK4))
% 3.84/1.08      | m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,X0_49),X0_48),u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) = X0_48 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2537]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_5491,plain,
% 3.84/1.08      ( ~ r4_lattice3(sK4,sK5,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | m1_subset_1(sK2(sK4,a_2_1_lattice3(sK4,sK6),sK5),u1_struct_0(sK4))
% 3.84/1.08      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = sK5 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_5489]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3216,plain,
% 3.84/1.08      ( k16_lattice3(sK4,sK6) != X0_48
% 3.84/1.08      | k16_lattice3(sK4,sK6) = sK5
% 3.84/1.08      | sK5 != X0_48 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2546]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3895,plain,
% 3.84/1.08      ( k16_lattice3(sK4,sK6) != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | k16_lattice3(sK4,sK6) = sK5
% 3.84/1.08      | sK5 != k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_3216]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3257,plain,
% 3.84/1.08      ( X0_48 != X1_48
% 3.84/1.08      | k16_lattice3(sK4,sK6) != X1_48
% 3.84/1.08      | k16_lattice3(sK4,sK6) = X0_48 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2546]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3397,plain,
% 3.84/1.08      ( X0_48 != k16_lattice3(sK4,sK6)
% 3.84/1.08      | k16_lattice3(sK4,sK6) = X0_48
% 3.84/1.08      | k16_lattice3(sK4,sK6) != k16_lattice3(sK4,sK6) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_3257]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3721,plain,
% 3.84/1.08      ( k16_lattice3(sK4,sK6) != k16_lattice3(sK4,sK6)
% 3.84/1.08      | k16_lattice3(sK4,sK6) = k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) != k16_lattice3(sK4,sK6) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_3397]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_3256,plain,
% 3.84/1.08      ( k16_lattice3(sK4,sK6) = k16_lattice3(sK4,sK6) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2545]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_13,plain,
% 3.84/1.08      ( v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0)
% 3.84/1.08      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
% 3.84/1.08      inference(cnf_transformation,[],[f54]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_453,plain,
% 3.84/1.08      ( v2_struct_0(X0)
% 3.84/1.08      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_454,plain,
% 3.84/1.08      ( v2_struct_0(sK4)
% 3.84/1.08      | k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_453]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_458,plain,
% 3.84/1.08      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0)) = k16_lattice3(sK4,X0) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_454,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2532,plain,
% 3.84/1.08      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,X0_49)) = k16_lattice3(sK4,X0_49) ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_458]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2581,plain,
% 3.84/1.08      ( k15_lattice3(sK4,a_2_1_lattice3(sK4,sK6)) = k16_lattice3(sK4,sK6) ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2532]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_18,negated_conjecture,
% 3.84/1.08      ( k16_lattice3(sK4,sK6) != sK5 ),
% 3.84/1.08      inference(cnf_transformation,[],[f66]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2543,negated_conjecture,
% 3.84/1.08      ( k16_lattice3(sK4,sK6) != sK5 ),
% 3.84/1.08      inference(subtyping,[status(esa)],[c_18]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_2558,plain,
% 3.84/1.08      ( sK5 = sK5 ),
% 3.84/1.08      inference(instantiation,[status(thm)],[c_2545]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_19,negated_conjecture,
% 3.84/1.08      ( r3_lattice3(sK4,sK5,sK6) ),
% 3.84/1.08      inference(cnf_transformation,[],[f65]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_14,plain,
% 3.84/1.08      ( ~ r3_lattice3(X0,X1,X2)
% 3.84/1.08      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | ~ l3_lattices(X0) ),
% 3.84/1.08      inference(cnf_transformation,[],[f69]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_432,plain,
% 3.84/1.08      ( ~ r3_lattice3(X0,X1,X2)
% 3.84/1.08      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.84/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.08      | v2_struct_0(X0)
% 3.84/1.08      | sK4 != X0 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_433,plain,
% 3.84/1.08      ( ~ r3_lattice3(sK4,X0,X1)
% 3.84/1.08      | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | v2_struct_0(sK4) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_432]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_437,plain,
% 3.84/1.08      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | ~ r3_lattice3(sK4,X0,X1) ),
% 3.84/1.08      inference(global_propositional_subsumption,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_433,c_25]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_438,plain,
% 3.84/1.08      ( ~ r3_lattice3(sK4,X0,X1)
% 3.84/1.08      | r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(renaming,[status(thm)],[c_437]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_772,plain,
% 3.84/1.08      ( r2_hidden(X0,a_2_1_lattice3(sK4,X1))
% 3.84/1.08      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.84/1.08      | sK5 != X0
% 3.84/1.08      | sK6 != X1
% 3.84/1.08      | sK4 != sK4 ),
% 3.84/1.08      inference(resolution_lifted,[status(thm)],[c_19,c_438]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_773,plain,
% 3.84/1.08      ( r2_hidden(sK5,a_2_1_lattice3(sK4,sK6))
% 3.84/1.08      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(unflattening,[status(thm)],[c_772]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_20,negated_conjecture,
% 3.84/1.08      ( r2_hidden(sK5,sK6) ),
% 3.84/1.08      inference(cnf_transformation,[],[f64]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(c_21,negated_conjecture,
% 3.84/1.08      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.84/1.08      inference(cnf_transformation,[],[f63]) ).
% 3.84/1.08  
% 3.84/1.08  cnf(contradiction,plain,
% 3.84/1.08      ( $false ),
% 3.84/1.08      inference(minisat,
% 3.84/1.08                [status(thm)],
% 3.84/1.08                [c_14729,c_11862,c_8242,c_7440,c_5713,c_5491,c_3895,
% 3.84/1.08                 c_3721,c_3256,c_2581,c_2543,c_2558,c_773,c_20,c_21]) ).
% 3.84/1.08  
% 3.84/1.08  
% 3.84/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.08  
% 3.84/1.08  ------                               Statistics
% 3.84/1.08  
% 3.84/1.08  ------ Selected
% 3.84/1.08  
% 3.84/1.08  total_time:                             0.528
% 3.84/1.08  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:15 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 814 expanded)
%              Number of clauses        :  121 ( 193 expanded)
%              Number of leaves         :   19 ( 262 expanded)
%              Depth                    :   21
%              Number of atoms          :  979 (5679 expanded)
%              Number of equality atoms :  124 ( 828 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK2(X0,X1,X2),X2)
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK2(X0,X1,X2),X2)
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
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
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
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

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k16_lattice3(X0,X2) != X1
          & r3_lattice3(X0,X1,X2)
          & r2_hidden(X1,X2) )
     => ( k16_lattice3(X0,sK6) != X1
        & r3_lattice3(X0,X1,sK6)
        & r2_hidden(X1,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f46,plain,
    ( k16_lattice3(sK4,sK6) != sK5
    & r3_lattice3(sK4,sK5,sK6)
    & r2_hidden(sK5,sK6)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f45,f44,f43])).

fof(f70,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
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
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
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
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X2) = X1
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_9_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f6,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    r3_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3381,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_3380,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_4473,plain,
    ( X0_50 != X1_50
    | X1_50 = X0_50 ),
    inference(resolution,[status(thm)],[c_3381,c_3380])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_800,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK2(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_801,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | sK2(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_25,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_805,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | sK2(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_28,c_27,c_25])).

cnf(c_3373,plain,
    ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
    | sK2(X0_50,sK4,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_805])).

cnf(c_5237,plain,
    ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
    | X0_50 = sK2(X0_50,sK4,X0_51) ),
    inference(resolution,[status(thm)],[c_4473,c_3373])).

cnf(c_3382,plain,
    ( ~ r3_lattice3(X0_49,X0_50,X0_51)
    | r3_lattice3(X0_49,X1_50,X0_51)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_5471,plain,
    ( r3_lattice3(X0_49,X0_50,X0_51)
    | ~ r3_lattice3(X0_49,sK2(X0_50,sK4,X1_51),X0_51)
    | ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X1_51)) ),
    inference(resolution,[status(thm)],[c_5237,c_3382])).

cnf(c_10,plain,
    ( r3_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_9_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_998,plain,
    ( r3_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_9_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_999,plain,
    ( r3_lattice3(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_998])).

cnf(c_1003,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | r3_lattice3(sK4,sK2(X0,sK4,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_999,c_28,c_27,c_25])).

cnf(c_1004,plain,
    ( r3_lattice3(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_1003])).

cnf(c_3364,plain,
    ( r3_lattice3(sK4,sK2(X0_50,sK4,X0_51),X0_51)
    | ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51)) ),
    inference(subtyping,[status(esa)],[c_1004])).

cnf(c_6202,plain,
    ( r3_lattice3(sK4,X0_50,X0_51)
    | ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51)) ),
    inference(resolution,[status(thm)],[c_5471,c_3364])).

cnf(c_5,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1229,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_1230,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1229])).

cnf(c_1234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1230,c_28])).

cnf(c_1235,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1234])).

cnf(c_3359,plain,
    ( r4_lattice3(sK4,X0_50,X0_51)
    | r2_hidden(sK1(sK4,X0_50,X0_51),X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1235])).

cnf(c_6302,plain,
    ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
    | r3_lattice3(sK4,sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_6202,c_3359])).

cnf(c_3,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1271,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_1272,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattice3(sK4,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1271])).

cnf(c_1276,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X2)
    | ~ r3_lattice3(sK4,X0,X2)
    | r1_lattices(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1272,c_28])).

cnf(c_1277,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattice3(sK4,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1276])).

cnf(c_3357,plain,
    ( r1_lattices(sK4,X0_50,X1_50)
    | ~ r3_lattice3(sK4,X0_50,X0_51)
    | ~ r2_hidden(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1277])).

cnf(c_6435,plain,
    ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
    | r1_lattices(sK4,sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),X1_50)
    | ~ r2_hidden(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_6302,c_3357])).

cnf(c_3384,plain,
    ( ~ m1_subset_1(X0_50,X0_52)
    | m1_subset_1(X1_50,X0_52)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_5469,plain,
    ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
    | m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(sK2(X0_50,sK4,X0_51),X0_52) ),
    inference(resolution,[status(thm)],[c_5237,c_3384])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_782,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_783,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_787,plain,
    ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_783,c_28,c_27,c_25])).

cnf(c_788,plain,
    ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_787])).

cnf(c_3374,plain,
    ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
    | m1_subset_1(sK2(X0_50,sK4,X0_51),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_788])).

cnf(c_6102,plain,
    ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
    | m1_subset_1(X0_50,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_5469,c_3374])).

cnf(c_6285,plain,
    ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_6102,c_3359])).

cnf(c_10761,plain,
    ( ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ r2_hidden(X1_50,X0_51)
    | r1_lattices(sK4,sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),X1_50)
    | r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6435,c_6285])).

cnf(c_10762,plain,
    ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
    | r1_lattices(sK4,sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),X1_50)
    | ~ r2_hidden(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_10761])).

cnf(c_4,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1250,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_1251,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1250])).

cnf(c_1255,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1251,c_28])).

cnf(c_1256,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1255])).

cnf(c_3358,plain,
    ( r4_lattice3(sK4,X0_50,X0_51)
    | ~ r1_lattices(sK4,sK1(sK4,X0_50,X0_51),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1256])).

cnf(c_10795,plain,
    ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_10762,c_3358])).

cnf(c_10797,plain,
    ( r4_lattice3(sK4,sK5,a_2_9_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_10795])).

cnf(c_4321,plain,
    ( X0_50 != X1_50
    | X0_50 = k15_lattice3(sK4,X0_51)
    | k15_lattice3(sK4,X0_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_3381])).

cnf(c_8050,plain,
    ( X0_50 != X1_50
    | X0_50 = k15_lattice3(sK4,a_2_9_lattice3(sK4,X0_51))
    | k15_lattice3(sK4,a_2_9_lattice3(sK4,X0_51)) != X1_50 ),
    inference(instantiation,[status(thm)],[c_4321])).

cnf(c_8051,plain,
    ( k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)) != sK5
    | sK5 = k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_8050])).

cnf(c_20,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_818,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_819,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_818])).

cnf(c_823,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X1)
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_819,c_28,c_27,c_25])).

cnf(c_824,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_823])).

cnf(c_3372,plain,
    ( ~ r4_lattice3(sK4,X0_50,X0_51)
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_824])).

cnf(c_7209,plain,
    ( ~ r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
    | ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_9_lattice3(sK4,X0_51)) = X0_50 ),
    inference(instantiation,[status(thm)],[c_3372])).

cnf(c_7211,plain,
    ( ~ r4_lattice3(sK4,sK5,a_2_9_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,a_2_9_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_7209])).

cnf(c_3386,plain,
    ( ~ r3_lattices(X0_49,X0_50,X1_50)
    | r3_lattices(X0_49,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_4211,plain,
    ( r3_lattices(sK4,X0_50,X1_50)
    | ~ r3_lattices(sK4,X2_50,k15_lattice3(sK4,X0_51))
    | X0_50 != X2_50
    | X1_50 != k15_lattice3(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_3386])).

cnf(c_4684,plain,
    ( ~ r3_lattices(sK4,X0_50,k15_lattice3(sK4,X0_51))
    | r3_lattices(sK4,sK3(sK4,X1_50,X1_51),X1_50)
    | X1_50 != k15_lattice3(sK4,X0_51)
    | sK3(sK4,X1_50,X1_51) != X0_50 ),
    inference(instantiation,[status(thm)],[c_4211])).

cnf(c_5275,plain,
    ( r3_lattices(sK4,sK3(sK4,X0_50,X0_51),X0_50)
    | ~ r3_lattices(sK4,sK3(sK4,X0_50,X0_51),k15_lattice3(sK4,X1_51))
    | X0_50 != k15_lattice3(sK4,X1_51)
    | sK3(sK4,X0_50,X0_51) != sK3(sK4,X0_50,X0_51) ),
    inference(instantiation,[status(thm)],[c_4684])).

cnf(c_6998,plain,
    ( r3_lattices(sK4,sK3(sK4,X0_50,X0_51),X0_50)
    | ~ r3_lattices(sK4,sK3(sK4,X0_50,X0_51),k15_lattice3(sK4,a_2_9_lattice3(sK4,X1_51)))
    | X0_50 != k15_lattice3(sK4,a_2_9_lattice3(sK4,X1_51))
    | sK3(sK4,X0_50,X0_51) != sK3(sK4,X0_50,X0_51) ),
    inference(instantiation,[status(thm)],[c_5275])).

cnf(c_7000,plain,
    ( ~ r3_lattices(sK4,sK3(sK4,sK5,sK6),k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)))
    | r3_lattices(sK4,sK3(sK4,sK5,sK6),sK5)
    | sK3(sK4,sK5,sK6) != sK3(sK4,sK5,sK6)
    | sK5 != k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_6998])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_9_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1016,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_9_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_1017,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_28,c_27,c_25])).

cnf(c_1022,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r2_hidden(X0,a_2_9_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1021])).

cnf(c_3363,plain,
    ( ~ r3_lattice3(sK4,X0_50,X0_51)
    | r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1022])).

cnf(c_6525,plain,
    ( ~ r3_lattice3(sK4,sK3(sK4,X0_50,X0_51),X1_51)
    | r2_hidden(sK3(sK4,X0_50,X0_51),a_2_9_lattice3(sK4,X1_51))
    | ~ m1_subset_1(sK3(sK4,X0_50,X0_51),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3363])).

cnf(c_6531,plain,
    ( ~ r3_lattice3(sK4,sK3(sK4,sK5,sK6),sK6)
    | r2_hidden(sK3(sK4,sK5,sK6),a_2_9_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK3(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6525])).

cnf(c_19,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_842,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_843,plain,
    ( r3_lattices(sK4,X0,k15_lattice3(sK4,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X1)
    | r3_lattices(sK4,X0,k15_lattice3(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_28,c_27,c_25])).

cnf(c_848,plain,
    ( r3_lattices(sK4,X0,k15_lattice3(sK4,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_847])).

cnf(c_3371,plain,
    ( r3_lattices(sK4,X0_50,k15_lattice3(sK4,X0_51))
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_848])).

cnf(c_6310,plain,
    ( r3_lattices(sK4,sK3(sK4,X0_50,X0_51),k15_lattice3(sK4,X1_51))
    | ~ r2_hidden(sK3(sK4,X0_50,X0_51),X1_51)
    | ~ m1_subset_1(sK3(sK4,X0_50,X0_51),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3371])).

cnf(c_6524,plain,
    ( r3_lattices(sK4,sK3(sK4,X0_50,X0_51),k15_lattice3(sK4,a_2_9_lattice3(sK4,X1_51)))
    | ~ r2_hidden(sK3(sK4,X0_50,X0_51),a_2_9_lattice3(sK4,X1_51))
    | ~ m1_subset_1(sK3(sK4,X0_50,X0_51),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6310])).

cnf(c_6527,plain,
    ( r3_lattices(sK4,sK3(sK4,sK5,sK6),k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)))
    | ~ r2_hidden(sK3(sK4,sK5,sK6),a_2_9_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK3(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6524])).

cnf(c_5276,plain,
    ( sK3(sK4,X0_50,X0_51) = sK3(sK4,X0_50,X0_51) ),
    inference(instantiation,[status(thm)],[c_3380])).

cnf(c_5281,plain,
    ( sK3(sK4,sK5,sK6) = sK3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_5276])).

cnf(c_3427,plain,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | r2_hidden(sK5,a_2_9_lattice3(sK4,sK6))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3363])).

cnf(c_13,plain,
    ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_974,plain,
    ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_975,plain,
    ( ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
    | ~ r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r3_lattice3(sK4,X0,X1)
    | ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_28,c_27,c_25])).

cnf(c_980,plain,
    ( ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
    | ~ r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_979])).

cnf(c_3365,plain,
    ( ~ r3_lattices(sK4,sK3(sK4,X0_50,X0_51),X0_50)
    | ~ r3_lattice3(sK4,X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_980])).

cnf(c_3421,plain,
    ( ~ r3_lattices(sK4,sK3(sK4,sK5,sK6),sK5)
    | ~ r3_lattice3(sK4,sK5,sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_3365])).

cnf(c_14,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_950,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_951,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_950])).

cnf(c_955,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
    | ~ r3_lattice3(sK4,X0,X1)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_951,c_28,c_27,c_25])).

cnf(c_956,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_955])).

cnf(c_3366,plain,
    ( ~ r3_lattice3(sK4,X0_50,X0_51)
    | r3_lattice3(sK4,sK3(sK4,X0_50,X0_51),X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_956])).

cnf(c_3418,plain,
    ( r3_lattice3(sK4,sK3(sK4,sK5,sK6),sK6)
    | ~ r3_lattice3(sK4,sK5,sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_3366])).

cnf(c_15,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_926,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_927,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_931,plain,
    ( m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r3_lattice3(sK4,X0,X1)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_927,c_28,c_27,c_25])).

cnf(c_932,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_931])).

cnf(c_3367,plain,
    ( ~ r3_lattice3(sK4,X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0_50,X0_51),u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_932])).

cnf(c_3415,plain,
    ( ~ r3_lattice3(sK4,sK5,sK6)
    | m1_subset_1(sK3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k16_lattice3(sK4,sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_3367])).

cnf(c_21,negated_conjecture,
    ( k16_lattice3(sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3378,negated_conjecture,
    ( k16_lattice3(sK4,sK6) != sK5 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3393,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3380])).

cnf(c_22,negated_conjecture,
    ( r3_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10797,c_8051,c_7211,c_7000,c_6531,c_6527,c_5281,c_3427,c_3421,c_3418,c_3415,c_3378,c_3393,c_22,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:17:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.39/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.01  
% 3.39/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.01  
% 3.39/1.01  ------  iProver source info
% 3.39/1.01  
% 3.39/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.01  git: non_committed_changes: false
% 3.39/1.01  git: last_make_outside_of_git: false
% 3.39/1.01  
% 3.39/1.01  ------ 
% 3.39/1.01  ------ Parsing...
% 3.39/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.01  
% 3.39/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.39/1.01  
% 3.39/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.01  
% 3.39/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.01  ------ Proving...
% 3.39/1.01  ------ Problem Properties 
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  clauses                                 25
% 3.39/1.01  conjectures                             4
% 3.39/1.01  EPR                                     2
% 3.39/1.01  Horn                                    19
% 3.39/1.01  unary                                   5
% 3.39/1.01  binary                                  4
% 3.39/1.01  lits                                    70
% 3.39/1.01  lits eq                                 6
% 3.39/1.01  fd_pure                                 0
% 3.39/1.01  fd_pseudo                               0
% 3.39/1.01  fd_cond                                 0
% 3.39/1.01  fd_pseudo_cond                          4
% 3.39/1.01  AC symbols                              0
% 3.39/1.01  
% 3.39/1.01  ------ Input Options Time Limit: Unbounded
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  ------ 
% 3.39/1.01  Current options:
% 3.39/1.01  ------ 
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  ------ Proving...
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  % SZS status Theorem for theBenchmark.p
% 3.39/1.01  
% 3.39/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.01  
% 3.39/1.01  fof(f4,axiom,(
% 3.39/1.01    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f16,plain,(
% 3.39/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 3.39/1.01    inference(ennf_transformation,[],[f4])).
% 3.39/1.01  
% 3.39/1.01  fof(f17,plain,(
% 3.39/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.39/1.01    inference(flattening,[],[f16])).
% 3.39/1.01  
% 3.39/1.01  fof(f34,plain,(
% 3.39/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.39/1.01    inference(nnf_transformation,[],[f17])).
% 3.39/1.01  
% 3.39/1.01  fof(f35,plain,(
% 3.39/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.39/1.01    inference(rectify,[],[f34])).
% 3.39/1.01  
% 3.39/1.01  fof(f36,plain,(
% 3.39/1.01    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.39/1.01    introduced(choice_axiom,[])).
% 3.39/1.01  
% 3.39/1.01  fof(f37,plain,(
% 3.39/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 3.39/1.01  
% 3.39/1.01  fof(f57,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f37])).
% 3.39/1.01  
% 3.39/1.01  fof(f8,conjecture,(
% 3.39/1.01    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 3.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f9,negated_conjecture,(
% 3.39/1.01    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 3.39/1.01    inference(negated_conjecture,[],[f8])).
% 3.39/1.01  
% 3.39/1.01  fof(f24,plain,(
% 3.39/1.01    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.39/1.01    inference(ennf_transformation,[],[f9])).
% 3.39/1.01  
% 3.39/1.01  fof(f25,plain,(
% 3.39/1.01    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.39/1.01    inference(flattening,[],[f24])).
% 3.39/1.01  
% 3.39/1.01  fof(f45,plain,(
% 3.39/1.01    ( ! [X0,X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => (k16_lattice3(X0,sK6) != X1 & r3_lattice3(X0,X1,sK6) & r2_hidden(X1,sK6))) )),
% 3.39/1.01    introduced(choice_axiom,[])).
% 3.39/1.01  
% 3.39/1.01  fof(f44,plain,(
% 3.39/1.01    ( ! [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k16_lattice3(X0,X2) != sK5 & r3_lattice3(X0,sK5,X2) & r2_hidden(sK5,X2)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.39/1.01    introduced(choice_axiom,[])).
% 3.39/1.01  
% 3.39/1.01  fof(f43,plain,(
% 3.39/1.01    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK4,X2) != X1 & r3_lattice3(sK4,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 3.39/1.01    introduced(choice_axiom,[])).
% 3.39/1.01  
% 3.39/1.01  fof(f46,plain,(
% 3.39/1.01    ((k16_lattice3(sK4,sK6) != sK5 & r3_lattice3(sK4,sK5,sK6) & r2_hidden(sK5,sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 3.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f45,f44,f43])).
% 3.39/1.01  
% 3.39/1.01  fof(f70,plain,(
% 3.39/1.01    v4_lattice3(sK4)),
% 3.39/1.01    inference(cnf_transformation,[],[f46])).
% 3.39/1.01  
% 3.39/1.01  fof(f68,plain,(
% 3.39/1.01    ~v2_struct_0(sK4)),
% 3.39/1.01    inference(cnf_transformation,[],[f46])).
% 3.39/1.01  
% 3.39/1.01  fof(f69,plain,(
% 3.39/1.01    v10_lattices(sK4)),
% 3.39/1.01    inference(cnf_transformation,[],[f46])).
% 3.39/1.01  
% 3.39/1.01  fof(f71,plain,(
% 3.39/1.01    l3_lattices(sK4)),
% 3.39/1.01    inference(cnf_transformation,[],[f46])).
% 3.39/1.01  
% 3.39/1.01  fof(f58,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK2(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f37])).
% 3.39/1.01  
% 3.39/1.01  fof(f2,axiom,(
% 3.39/1.01    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f12,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.39/1.01    inference(ennf_transformation,[],[f2])).
% 3.39/1.01  
% 3.39/1.01  fof(f13,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(flattening,[],[f12])).
% 3.39/1.01  
% 3.39/1.01  fof(f30,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(nnf_transformation,[],[f13])).
% 3.39/1.01  
% 3.39/1.01  fof(f31,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(rectify,[],[f30])).
% 3.39/1.01  
% 3.39/1.01  fof(f32,plain,(
% 3.39/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.39/1.01    introduced(choice_axiom,[])).
% 3.39/1.01  
% 3.39/1.01  fof(f33,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.39/1.01  
% 3.39/1.01  fof(f53,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f33])).
% 3.39/1.01  
% 3.39/1.01  fof(f1,axiom,(
% 3.39/1.01    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f10,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.39/1.01    inference(ennf_transformation,[],[f1])).
% 3.39/1.01  
% 3.39/1.01  fof(f11,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(flattening,[],[f10])).
% 3.39/1.01  
% 3.39/1.01  fof(f26,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(nnf_transformation,[],[f11])).
% 3.39/1.01  
% 3.39/1.01  fof(f27,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(rectify,[],[f26])).
% 3.39/1.01  
% 3.39/1.01  fof(f28,plain,(
% 3.39/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.39/1.01    introduced(choice_axiom,[])).
% 3.39/1.01  
% 3.39/1.01  fof(f29,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.39/1.01  
% 3.39/1.01  fof(f47,plain,(
% 3.39/1.01    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f29])).
% 3.39/1.01  
% 3.39/1.01  fof(f56,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f37])).
% 3.39/1.01  
% 3.39/1.01  fof(f54,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f33])).
% 3.39/1.01  
% 3.39/1.01  fof(f7,axiom,(
% 3.39/1.01    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 3.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f22,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.39/1.01    inference(ennf_transformation,[],[f7])).
% 3.39/1.01  
% 3.39/1.01  fof(f23,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(flattening,[],[f22])).
% 3.39/1.01  
% 3.39/1.01  fof(f67,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f23])).
% 3.39/1.01  
% 3.39/1.01  fof(f59,plain,(
% 3.39/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f37])).
% 3.39/1.01  
% 3.39/1.01  fof(f76,plain,(
% 3.39/1.01    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_9_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.39/1.01    inference(equality_resolution,[],[f59])).
% 3.39/1.01  
% 3.39/1.01  fof(f6,axiom,(
% 3.39/1.01    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 3.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f20,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.39/1.01    inference(ennf_transformation,[],[f6])).
% 3.39/1.01  
% 3.39/1.01  fof(f21,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(flattening,[],[f20])).
% 3.39/1.01  
% 3.39/1.01  fof(f65,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f21])).
% 3.39/1.01  
% 3.39/1.01  fof(f5,axiom,(
% 3.39/1.01    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 3.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f18,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.39/1.01    inference(ennf_transformation,[],[f5])).
% 3.39/1.01  
% 3.39/1.01  fof(f19,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(flattening,[],[f18])).
% 3.39/1.01  
% 3.39/1.01  fof(f38,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(nnf_transformation,[],[f19])).
% 3.39/1.01  
% 3.39/1.01  fof(f39,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(flattening,[],[f38])).
% 3.39/1.01  
% 3.39/1.01  fof(f40,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(rectify,[],[f39])).
% 3.39/1.01  
% 3.39/1.01  fof(f41,plain,(
% 3.39/1.01    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.39/1.01    introduced(choice_axiom,[])).
% 3.39/1.01  
% 3.39/1.01  fof(f42,plain,(
% 3.39/1.01    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 3.39/1.01  
% 3.39/1.01  fof(f64,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | ~r3_lattices(X0,sK3(X0,X1,X2),X1) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f42])).
% 3.39/1.01  
% 3.39/1.01  fof(f63,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | r3_lattice3(X0,sK3(X0,X1,X2),X2) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f42])).
% 3.39/1.01  
% 3.39/1.01  fof(f62,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f42])).
% 3.39/1.01  
% 3.39/1.01  fof(f75,plain,(
% 3.39/1.01    k16_lattice3(sK4,sK6) != sK5),
% 3.39/1.01    inference(cnf_transformation,[],[f46])).
% 3.39/1.01  
% 3.39/1.01  fof(f74,plain,(
% 3.39/1.01    r3_lattice3(sK4,sK5,sK6)),
% 3.39/1.01    inference(cnf_transformation,[],[f46])).
% 3.39/1.01  
% 3.39/1.01  fof(f73,plain,(
% 3.39/1.01    r2_hidden(sK5,sK6)),
% 3.39/1.01    inference(cnf_transformation,[],[f46])).
% 3.39/1.01  
% 3.39/1.01  fof(f72,plain,(
% 3.39/1.01    m1_subset_1(sK5,u1_struct_0(sK4))),
% 3.39/1.01    inference(cnf_transformation,[],[f46])).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3381,plain,
% 3.39/1.01      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 3.39/1.01      theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3380,plain,( X0_50 = X0_50 ),theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4473,plain,
% 3.39/1.01      ( X0_50 != X1_50 | X1_50 = X0_50 ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_3381,c_3380]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_11,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
% 3.39/1.01      | ~ v10_lattices(X1)
% 3.39/1.01      | ~ v4_lattice3(X1)
% 3.39/1.01      | v2_struct_0(X1)
% 3.39/1.01      | ~ l3_lattices(X1)
% 3.39/1.01      | sK2(X0,X1,X2) = X0 ),
% 3.39/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_26,negated_conjecture,
% 3.39/1.01      ( v4_lattice3(sK4) ),
% 3.39/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_800,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
% 3.39/1.01      | ~ v10_lattices(X1)
% 3.39/1.01      | v2_struct_0(X1)
% 3.39/1.01      | ~ l3_lattices(X1)
% 3.39/1.01      | sK2(X0,X1,X2) = X0
% 3.39/1.01      | sK4 != X1 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_801,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4)
% 3.39/1.01      | sK2(X0,sK4,X1) = X0 ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_800]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_28,negated_conjecture,
% 3.39/1.01      ( ~ v2_struct_0(sK4) ),
% 3.39/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_27,negated_conjecture,
% 3.39/1.01      ( v10_lattices(sK4) ),
% 3.39/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_25,negated_conjecture,
% 3.39/1.01      ( l3_lattices(sK4) ),
% 3.39/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_805,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1)) | sK2(X0,sK4,X1) = X0 ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_801,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3373,plain,
% 3.39/1.01      ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | sK2(X0_50,sK4,X0_51) = X0_50 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_805]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5237,plain,
% 3.39/1.01      ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | X0_50 = sK2(X0_50,sK4,X0_51) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_4473,c_3373]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3382,plain,
% 3.39/1.01      ( ~ r3_lattice3(X0_49,X0_50,X0_51)
% 3.39/1.01      | r3_lattice3(X0_49,X1_50,X0_51)
% 3.39/1.01      | X1_50 != X0_50 ),
% 3.39/1.01      theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5471,plain,
% 3.39/1.01      ( r3_lattice3(X0_49,X0_50,X0_51)
% 3.39/1.01      | ~ r3_lattice3(X0_49,sK2(X0_50,sK4,X1_51),X0_51)
% 3.39/1.01      | ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X1_51)) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_5237,c_3382]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_10,plain,
% 3.39/1.01      ( r3_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.39/1.01      | ~ r2_hidden(X1,a_2_9_lattice3(X0,X2))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | ~ v4_lattice3(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_998,plain,
% 3.39/1.01      ( r3_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.39/1.01      | ~ r2_hidden(X1,a_2_9_lattice3(X0,X2))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_999,plain,
% 3.39/1.01      ( r3_lattice3(sK4,sK2(X0,sK4,X1),X1)
% 3.39/1.01      | ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4) ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_998]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1003,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
% 3.39/1.01      | r3_lattice3(sK4,sK2(X0,sK4,X1),X1) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_999,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1004,plain,
% 3.39/1.01      ( r3_lattice3(sK4,sK2(X0,sK4,X1),X1)
% 3.39/1.01      | ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1)) ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_1003]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3364,plain,
% 3.39/1.01      ( r3_lattice3(sK4,sK2(X0_50,sK4,X0_51),X0_51)
% 3.39/1.01      | ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_1004]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6202,plain,
% 3.39/1.01      ( r3_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51)) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_5471,c_3364]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5,plain,
% 3.39/1.01      ( r4_lattice3(X0,X1,X2)
% 3.39/1.01      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1229,plain,
% 3.39/1.01      ( r4_lattice3(X0,X1,X2)
% 3.39/1.01      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1230,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0,X1)
% 3.39/1.01      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | v2_struct_0(sK4) ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_1229]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1234,plain,
% 3.39/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.39/1.01      | r4_lattice3(sK4,X0,X1) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_1230,c_28]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1235,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0,X1)
% 3.39/1.01      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_1234]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3359,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | r2_hidden(sK1(sK4,X0_50,X0_51),X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_1235]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6302,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | r3_lattice3(sK4,sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_6202,c_3359]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3,plain,
% 3.39/1.01      ( r1_lattices(X0,X1,X2)
% 3.39/1.01      | ~ r3_lattice3(X0,X1,X3)
% 3.39/1.01      | ~ r2_hidden(X2,X3)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1271,plain,
% 3.39/1.01      ( r1_lattices(X0,X1,X2)
% 3.39/1.01      | ~ r3_lattice3(X0,X1,X3)
% 3.39/1.01      | ~ r2_hidden(X2,X3)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1272,plain,
% 3.39/1.01      ( r1_lattices(sK4,X0,X1)
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X2)
% 3.39/1.01      | ~ r2_hidden(X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.39/1.01      | v2_struct_0(sK4) ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_1271]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1276,plain,
% 3.39/1.01      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ r2_hidden(X1,X2)
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X2)
% 3.39/1.01      | r1_lattices(sK4,X0,X1) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_1272,c_28]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1277,plain,
% 3.39/1.01      ( r1_lattices(sK4,X0,X1)
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X2)
% 3.39/1.01      | ~ r2_hidden(X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_1276]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3357,plain,
% 3.39/1.01      ( r1_lattices(sK4,X0_50,X1_50)
% 3.39/1.01      | ~ r3_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | ~ r2_hidden(X1_50,X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_1277]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6435,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | r1_lattices(sK4,sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),X1_50)
% 3.39/1.01      | ~ r2_hidden(X1_50,X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_6302,c_3357]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3384,plain,
% 3.39/1.01      ( ~ m1_subset_1(X0_50,X0_52)
% 3.39/1.01      | m1_subset_1(X1_50,X0_52)
% 3.39/1.01      | X1_50 != X0_50 ),
% 3.39/1.01      theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5469,plain,
% 3.39/1.01      ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | m1_subset_1(X0_50,X0_52)
% 3.39/1.01      | ~ m1_subset_1(sK2(X0_50,sK4,X0_51),X0_52) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_5237,c_3384]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_12,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
% 3.39/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.39/1.01      | ~ v10_lattices(X1)
% 3.39/1.01      | ~ v4_lattice3(X1)
% 3.39/1.01      | v2_struct_0(X1)
% 3.39/1.01      | ~ l3_lattices(X1) ),
% 3.39/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_782,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
% 3.39/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.39/1.01      | ~ v10_lattices(X1)
% 3.39/1.01      | v2_struct_0(X1)
% 3.39/1.01      | ~ l3_lattices(X1)
% 3.39/1.01      | sK4 != X1 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_783,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
% 3.39/1.01      | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4) ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_782]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_787,plain,
% 3.39/1.01      ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
% 3.39/1.01      | ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1)) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_783,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_788,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,a_2_9_lattice3(sK4,X1))
% 3.39/1.01      | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_787]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3374,plain,
% 3.39/1.01      ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | m1_subset_1(sK2(X0_50,sK4,X0_51),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_788]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6102,plain,
% 3.39/1.01      ( ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | m1_subset_1(X0_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_5469,c_3374]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6285,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | m1_subset_1(sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_6102,c_3359]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_10761,plain,
% 3.39/1.01      ( ~ m1_subset_1(X1_50,u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | ~ r2_hidden(X1_50,X0_51)
% 3.39/1.01      | r1_lattices(sK4,sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),X1_50)
% 3.39/1.01      | r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_6435,c_6285]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_10762,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | r1_lattices(sK4,sK1(sK4,X0_50,a_2_9_lattice3(sK4,X0_51)),X1_50)
% 3.39/1.01      | ~ r2_hidden(X1_50,X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_10761]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4,plain,
% 3.39/1.01      ( r4_lattice3(X0,X1,X2)
% 3.39/1.01      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1250,plain,
% 3.39/1.01      ( r4_lattice3(X0,X1,X2)
% 3.39/1.01      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1251,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | v2_struct_0(sK4) ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_1250]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1255,plain,
% 3.39/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.39/1.01      | r4_lattice3(sK4,X0,X1) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_1251,c_28]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1256,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_1255]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3358,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | ~ r1_lattices(sK4,sK1(sK4,X0_50,X0_51),X0_50)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_1256]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_10795,plain,
% 3.39/1.01      ( r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | ~ r2_hidden(X0_50,X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_10762,c_3358]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_10797,plain,
% 3.39/1.01      ( r4_lattice3(sK4,sK5,a_2_9_lattice3(sK4,sK6))
% 3.39/1.01      | ~ r2_hidden(sK5,sK6)
% 3.39/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_10795]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4321,plain,
% 3.39/1.01      ( X0_50 != X1_50
% 3.39/1.01      | X0_50 = k15_lattice3(sK4,X0_51)
% 3.39/1.01      | k15_lattice3(sK4,X0_51) != X1_50 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3381]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_8050,plain,
% 3.39/1.01      ( X0_50 != X1_50
% 3.39/1.01      | X0_50 = k15_lattice3(sK4,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | k15_lattice3(sK4,a_2_9_lattice3(sK4,X0_51)) != X1_50 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_4321]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_8051,plain,
% 3.39/1.01      ( k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)) != sK5
% 3.39/1.01      | sK5 = k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6))
% 3.39/1.01      | sK5 != sK5 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_8050]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_20,plain,
% 3.39/1.01      ( ~ r4_lattice3(X0,X1,X2)
% 3.39/1.01      | ~ r2_hidden(X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | ~ v4_lattice3(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | k15_lattice3(X0,X2) = X1 ),
% 3.39/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_818,plain,
% 3.39/1.01      ( ~ r4_lattice3(X0,X1,X2)
% 3.39/1.01      | ~ r2_hidden(X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | k15_lattice3(X0,X2) = X1
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_819,plain,
% 3.39/1.01      ( ~ r4_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ r2_hidden(X0,X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4)
% 3.39/1.01      | k15_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_818]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_823,plain,
% 3.39/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ r2_hidden(X0,X1)
% 3.39/1.01      | ~ r4_lattice3(sK4,X0,X1)
% 3.39/1.01      | k15_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_819,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_824,plain,
% 3.39/1.01      ( ~ r4_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ r2_hidden(X0,X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | k15_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_823]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3372,plain,
% 3.39/1.01      ( ~ r4_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | ~ r2_hidden(X0_50,X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | k15_lattice3(sK4,X0_51) = X0_50 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_824]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_7209,plain,
% 3.39/1.01      ( ~ r4_lattice3(sK4,X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | ~ r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | k15_lattice3(sK4,a_2_9_lattice3(sK4,X0_51)) = X0_50 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3372]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_7211,plain,
% 3.39/1.01      ( ~ r4_lattice3(sK4,sK5,a_2_9_lattice3(sK4,sK6))
% 3.39/1.01      | ~ r2_hidden(sK5,a_2_9_lattice3(sK4,sK6))
% 3.39/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.39/1.01      | k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)) = sK5 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_7209]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3386,plain,
% 3.39/1.01      ( ~ r3_lattices(X0_49,X0_50,X1_50)
% 3.39/1.01      | r3_lattices(X0_49,X2_50,X3_50)
% 3.39/1.01      | X2_50 != X0_50
% 3.39/1.01      | X3_50 != X1_50 ),
% 3.39/1.01      theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4211,plain,
% 3.39/1.01      ( r3_lattices(sK4,X0_50,X1_50)
% 3.39/1.01      | ~ r3_lattices(sK4,X2_50,k15_lattice3(sK4,X0_51))
% 3.39/1.01      | X0_50 != X2_50
% 3.39/1.01      | X1_50 != k15_lattice3(sK4,X0_51) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3386]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4684,plain,
% 3.39/1.01      ( ~ r3_lattices(sK4,X0_50,k15_lattice3(sK4,X0_51))
% 3.39/1.01      | r3_lattices(sK4,sK3(sK4,X1_50,X1_51),X1_50)
% 3.39/1.01      | X1_50 != k15_lattice3(sK4,X0_51)
% 3.39/1.01      | sK3(sK4,X1_50,X1_51) != X0_50 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_4211]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5275,plain,
% 3.39/1.01      ( r3_lattices(sK4,sK3(sK4,X0_50,X0_51),X0_50)
% 3.39/1.01      | ~ r3_lattices(sK4,sK3(sK4,X0_50,X0_51),k15_lattice3(sK4,X1_51))
% 3.39/1.01      | X0_50 != k15_lattice3(sK4,X1_51)
% 3.39/1.01      | sK3(sK4,X0_50,X0_51) != sK3(sK4,X0_50,X0_51) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_4684]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6998,plain,
% 3.39/1.01      ( r3_lattices(sK4,sK3(sK4,X0_50,X0_51),X0_50)
% 3.39/1.01      | ~ r3_lattices(sK4,sK3(sK4,X0_50,X0_51),k15_lattice3(sK4,a_2_9_lattice3(sK4,X1_51)))
% 3.39/1.01      | X0_50 != k15_lattice3(sK4,a_2_9_lattice3(sK4,X1_51))
% 3.39/1.01      | sK3(sK4,X0_50,X0_51) != sK3(sK4,X0_50,X0_51) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_5275]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_7000,plain,
% 3.39/1.01      ( ~ r3_lattices(sK4,sK3(sK4,sK5,sK6),k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)))
% 3.39/1.01      | r3_lattices(sK4,sK3(sK4,sK5,sK6),sK5)
% 3.39/1.01      | sK3(sK4,sK5,sK6) != sK3(sK4,sK5,sK6)
% 3.39/1.01      | sK5 != k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_6998]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_9,plain,
% 3.39/1.01      ( ~ r3_lattice3(X0,X1,X2)
% 3.39/1.01      | r2_hidden(X1,a_2_9_lattice3(X0,X2))
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | ~ v4_lattice3(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1016,plain,
% 3.39/1.01      ( ~ r3_lattice3(X0,X1,X2)
% 3.39/1.01      | r2_hidden(X1,a_2_9_lattice3(X0,X2))
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1017,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | r2_hidden(X0,a_2_9_lattice3(sK4,X1))
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4) ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_1016]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1021,plain,
% 3.39/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | r2_hidden(X0,a_2_9_lattice3(sK4,X1))
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X1) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_1017,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1022,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | r2_hidden(X0,a_2_9_lattice3(sK4,X1))
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_1021]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3363,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | r2_hidden(X0_50,a_2_9_lattice3(sK4,X0_51))
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_1022]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6525,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,sK3(sK4,X0_50,X0_51),X1_51)
% 3.39/1.01      | r2_hidden(sK3(sK4,X0_50,X0_51),a_2_9_lattice3(sK4,X1_51))
% 3.39/1.01      | ~ m1_subset_1(sK3(sK4,X0_50,X0_51),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3363]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6531,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,sK3(sK4,sK5,sK6),sK6)
% 3.39/1.01      | r2_hidden(sK3(sK4,sK5,sK6),a_2_9_lattice3(sK4,sK6))
% 3.39/1.01      | ~ m1_subset_1(sK3(sK4,sK5,sK6),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_6525]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_19,plain,
% 3.39/1.01      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 3.39/1.01      | ~ r2_hidden(X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | ~ v4_lattice3(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_842,plain,
% 3.39/1.01      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 3.39/1.01      | ~ r2_hidden(X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_843,plain,
% 3.39/1.01      ( r3_lattices(sK4,X0,k15_lattice3(sK4,X1))
% 3.39/1.01      | ~ r2_hidden(X0,X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4) ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_842]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_847,plain,
% 3.39/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ r2_hidden(X0,X1)
% 3.39/1.01      | r3_lattices(sK4,X0,k15_lattice3(sK4,X1)) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_843,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_848,plain,
% 3.39/1.01      ( r3_lattices(sK4,X0,k15_lattice3(sK4,X1))
% 3.39/1.01      | ~ r2_hidden(X0,X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_847]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3371,plain,
% 3.39/1.01      ( r3_lattices(sK4,X0_50,k15_lattice3(sK4,X0_51))
% 3.39/1.01      | ~ r2_hidden(X0_50,X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_848]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6310,plain,
% 3.39/1.01      ( r3_lattices(sK4,sK3(sK4,X0_50,X0_51),k15_lattice3(sK4,X1_51))
% 3.39/1.01      | ~ r2_hidden(sK3(sK4,X0_50,X0_51),X1_51)
% 3.39/1.01      | ~ m1_subset_1(sK3(sK4,X0_50,X0_51),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3371]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6524,plain,
% 3.39/1.01      ( r3_lattices(sK4,sK3(sK4,X0_50,X0_51),k15_lattice3(sK4,a_2_9_lattice3(sK4,X1_51)))
% 3.39/1.01      | ~ r2_hidden(sK3(sK4,X0_50,X0_51),a_2_9_lattice3(sK4,X1_51))
% 3.39/1.01      | ~ m1_subset_1(sK3(sK4,X0_50,X0_51),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_6310]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6527,plain,
% 3.39/1.01      ( r3_lattices(sK4,sK3(sK4,sK5,sK6),k15_lattice3(sK4,a_2_9_lattice3(sK4,sK6)))
% 3.39/1.01      | ~ r2_hidden(sK3(sK4,sK5,sK6),a_2_9_lattice3(sK4,sK6))
% 3.39/1.01      | ~ m1_subset_1(sK3(sK4,sK5,sK6),u1_struct_0(sK4)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_6524]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5276,plain,
% 3.39/1.01      ( sK3(sK4,X0_50,X0_51) = sK3(sK4,X0_50,X0_51) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3380]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5281,plain,
% 3.39/1.01      ( sK3(sK4,sK5,sK6) = sK3(sK4,sK5,sK6) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_5276]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3427,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,sK5,sK6)
% 3.39/1.01      | r2_hidden(sK5,a_2_9_lattice3(sK4,sK6))
% 3.39/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3363]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_13,plain,
% 3.39/1.01      ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
% 3.39/1.01      | ~ r3_lattice3(X0,X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | ~ v4_lattice3(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | k16_lattice3(X0,X2) = X1 ),
% 3.39/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_974,plain,
% 3.39/1.01      ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
% 3.39/1.01      | ~ r3_lattice3(X0,X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | k16_lattice3(X0,X2) = X1
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_975,plain,
% 3.39/1.01      ( ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4)
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_974]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_979,plain,
% 3.39/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_975,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_980,plain,
% 3.39/1.01      ( ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_979]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3365,plain,
% 3.39/1.01      ( ~ r3_lattices(sK4,sK3(sK4,X0_50,X0_51),X0_50)
% 3.39/1.01      | ~ r3_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,X0_51) = X0_50 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_980]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3421,plain,
% 3.39/1.01      ( ~ r3_lattices(sK4,sK3(sK4,sK5,sK6),sK5)
% 3.39/1.01      | ~ r3_lattice3(sK4,sK5,sK6)
% 3.39/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,sK6) = sK5 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3365]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_14,plain,
% 3.39/1.01      ( ~ r3_lattice3(X0,X1,X2)
% 3.39/1.01      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | ~ v4_lattice3(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | k16_lattice3(X0,X2) = X1 ),
% 3.39/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_950,plain,
% 3.39/1.01      ( ~ r3_lattice3(X0,X1,X2)
% 3.39/1.01      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | k16_lattice3(X0,X2) = X1
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_951,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4)
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_950]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_955,plain,
% 3.39/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_951,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_956,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_955]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3366,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | r3_lattice3(sK4,sK3(sK4,X0_50,X0_51),X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,X0_51) = X0_50 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_956]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3418,plain,
% 3.39/1.01      ( r3_lattice3(sK4,sK3(sK4,sK5,sK6),sK6)
% 3.39/1.01      | ~ r3_lattice3(sK4,sK5,sK6)
% 3.39/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,sK6) = sK5 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3366]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_15,plain,
% 3.39/1.01      ( ~ r3_lattice3(X0,X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | ~ v4_lattice3(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | k16_lattice3(X0,X2) = X1 ),
% 3.39/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_926,plain,
% 3.39/1.01      ( ~ r3_lattice3(X0,X1,X2)
% 3.39/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.39/1.01      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 3.39/1.01      | ~ v10_lattices(X0)
% 3.39/1.01      | v2_struct_0(X0)
% 3.39/1.01      | ~ l3_lattices(X0)
% 3.39/1.01      | k16_lattice3(X0,X2) = X1
% 3.39/1.01      | sK4 != X0 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_927,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
% 3.39/1.01      | ~ v10_lattices(sK4)
% 3.39/1.01      | v2_struct_0(sK4)
% 3.39/1.01      | ~ l3_lattices(sK4)
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_926]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_931,plain,
% 3.39/1.01      ( m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_927,c_28,c_27,c_25]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_932,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0,X1)
% 3.39/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.39/1.01      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,X1) = X0 ),
% 3.39/1.01      inference(renaming,[status(thm)],[c_931]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3367,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,X0_50,X0_51)
% 3.39/1.01      | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
% 3.39/1.01      | m1_subset_1(sK3(sK4,X0_50,X0_51),u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,X0_51) = X0_50 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_932]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3415,plain,
% 3.39/1.01      ( ~ r3_lattice3(sK4,sK5,sK6)
% 3.39/1.01      | m1_subset_1(sK3(sK4,sK5,sK6),u1_struct_0(sK4))
% 3.39/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.39/1.01      | k16_lattice3(sK4,sK6) = sK5 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3367]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_21,negated_conjecture,
% 3.39/1.01      ( k16_lattice3(sK4,sK6) != sK5 ),
% 3.39/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3378,negated_conjecture,
% 3.39/1.01      ( k16_lattice3(sK4,sK6) != sK5 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3393,plain,
% 3.39/1.01      ( sK5 = sK5 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_3380]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_22,negated_conjecture,
% 3.39/1.01      ( r3_lattice3(sK4,sK5,sK6) ),
% 3.39/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_23,negated_conjecture,
% 3.39/1.01      ( r2_hidden(sK5,sK6) ),
% 3.39/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_24,negated_conjecture,
% 3.39/1.01      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.39/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(contradiction,plain,
% 3.39/1.01      ( $false ),
% 3.39/1.01      inference(minisat,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_10797,c_8051,c_7211,c_7000,c_6531,c_6527,c_5281,
% 3.39/1.01                 c_3427,c_3421,c_3418,c_3415,c_3378,c_3393,c_22,c_23,
% 3.39/1.01                 c_24]) ).
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.01  
% 3.39/1.01  ------                               Statistics
% 3.39/1.01  
% 3.39/1.01  ------ Selected
% 3.39/1.01  
% 3.39/1.01  total_time:                             0.316
% 3.39/1.01  
%------------------------------------------------------------------------------

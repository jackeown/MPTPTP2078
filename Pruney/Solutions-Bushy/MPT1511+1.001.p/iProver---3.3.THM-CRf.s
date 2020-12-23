%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1511+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:45 EST 2020

% Result     : Theorem 15.50s
% Output     : CNFRefutation 15.50s
% Verified   : 
% Statistics : Number of formulae       :  262 (1353 expanded)
%              Number of clauses        :  181 ( 352 expanded)
%              Number of leaves         :   19 ( 321 expanded)
%              Depth                    :   17
%              Number of atoms          : 1341 (8636 expanded)
%              Number of equality atoms :  204 (1763 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattices(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattices(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,sK3(X0,X1,X2))
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,X2,sK3(X0,X1,X2))
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X1,X2,sK3(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
              & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
            | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
            | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
            | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( k16_lattice3(X0,a_2_4_lattice3(X0,sK5)) != sK5
          | k15_lattice3(X0,a_2_3_lattice3(X0,sK5)) != sK5 )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
              | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k16_lattice3(sK4,a_2_4_lattice3(sK4,X1)) != X1
            | k15_lattice3(sK4,a_2_3_lattice3(sK4,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( k16_lattice3(sK4,a_2_4_lattice3(sK4,sK5)) != sK5
      | k15_lattice3(sK4,a_2_3_lattice3(sK4,sK5)) != sK5 )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f53,f52])).

fof(f82,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattices(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattices(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,sK2(X0,X1,X2),X2)
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,sK2(X0,X1,X2),X2)
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X2) = X1
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X1,sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f58,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f56,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
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
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
              | ~ r3_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
              | ~ r3_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      | ~ r3_lattices(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_3_lattice3(X1,X2))
      | ~ r3_lattices(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ r3_lattices(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_4_lattice3(X1,X2))
      | ~ r3_lattices(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f85,plain,
    ( k16_lattice3(sK4,a_2_4_lattice3(sK4,sK5)) != sK5
    | k15_lattice3(sK4,a_2_3_lattice3(sK4,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,plain,
    ( r3_lattices(X0,X1,sK3(X2,X0,X1))
    | ~ r2_hidden(X2,a_2_4_lattice3(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_995,plain,
    ( r3_lattices(X0,X1,sK3(X2,X0,X1))
    | ~ r2_hidden(X2,a_2_4_lattice3(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_996,plain,
    ( r3_lattices(sK4,X0,sK3(X1,sK4,X0))
    | ~ r2_hidden(X1,a_2_4_lattice3(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_27,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_4_lattice3(sK4,X0))
    | r3_lattices(sK4,X0,sK3(X1,sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_30,c_29,c_27])).

cnf(c_1001,plain,
    ( r3_lattices(sK4,X0,sK3(X1,sK4,X0))
    | ~ r2_hidden(X1,a_2_4_lattice3(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1000])).

cnf(c_4937,plain,
    ( r3_lattices(sK4,X0_53,sK3(X1_53,sK4,X0_53))
    | ~ r2_hidden(X1_53,a_2_4_lattice3(sK4,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1001])).

cnf(c_61760,plain,
    ( r3_lattices(sK4,X0_53,sK3(sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)),sK4,X0_53))
    | ~ r2_hidden(sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)),a_2_4_lattice3(sK4,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4937])).

cnf(c_61762,plain,
    ( r3_lattices(sK4,sK5,sK3(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),sK4,sK5))
    | ~ r2_hidden(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),a_2_4_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_61760])).

cnf(c_4957,plain,
    ( ~ r3_lattices(X0_52,X0_53,X1_53)
    | r3_lattices(X0_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_6562,plain,
    ( ~ r3_lattices(sK4,X0_53,X1_53)
    | r3_lattices(sK4,X2_53,sK0(sK4,X2_53,a_2_4_lattice3(sK4,X3_53)))
    | X2_53 != X0_53
    | sK0(sK4,X2_53,a_2_4_lattice3(sK4,X3_53)) != X1_53 ),
    inference(instantiation,[status(thm)],[c_4957])).

cnf(c_22359,plain,
    ( ~ r3_lattices(sK4,X0_53,sK3(sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)),sK4,X3_53))
    | r3_lattices(sK4,X1_53,sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)))
    | X1_53 != X0_53
    | sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)) != sK3(sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)),sK4,X3_53) ),
    inference(instantiation,[status(thm)],[c_6562])).

cnf(c_22366,plain,
    ( ~ r3_lattices(sK4,sK5,sK3(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),sK4,sK5))
    | r3_lattices(sK4,sK5,sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)))
    | sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)) != sK3(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),sK4,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_22359])).

cnf(c_4952,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_6896,plain,
    ( X0_53 != X1_53
    | sK0(sK4,X2_53,a_2_4_lattice3(sK4,X3_53)) != X1_53
    | sK0(sK4,X2_53,a_2_4_lattice3(sK4,X3_53)) = X0_53 ),
    inference(instantiation,[status(thm)],[c_4952])).

cnf(c_10262,plain,
    ( X0_53 != sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53))
    | sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)) = X0_53
    | sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)) != sK0(sK4,X1_53,a_2_4_lattice3(sK4,X2_53)) ),
    inference(instantiation,[status(thm)],[c_6896])).

cnf(c_17092,plain,
    ( sK3(sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)),sK4,X2_53) != sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53))
    | sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)) = sK3(sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)),sK4,X2_53)
    | sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)) != sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)) ),
    inference(instantiation,[status(thm)],[c_10262])).

cnf(c_17094,plain,
    ( sK3(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),sK4,sK5) != sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5))
    | sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)) = sK3(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),sK4,sK5)
    | sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)) != sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_17092])).

cnf(c_9,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1260,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_1261,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1260])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1261,c_27])).

cnf(c_1266,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1265])).

cnf(c_4928,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1266])).

cnf(c_5422,plain,
    ( r4_lattice3(sK4,X0_53,X0_54) = iProver_top
    | r2_hidden(sK1(sK4,X0_53,X0_54),X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4928])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,a_2_3_lattice3(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_926,plain,
    ( ~ r2_hidden(X0,a_2_3_lattice3(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_927,plain,
    ( ~ r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | sK2(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_931,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | sK2(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_927,c_30,c_29,c_27])).

cnf(c_932,plain,
    ( ~ r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | sK2(X0,sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_931])).

cnf(c_4940,plain,
    ( ~ r2_hidden(X0_53,a_2_3_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | sK2(X0_53,sK4,X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_932])).

cnf(c_5408,plain,
    ( sK2(X0_53,sK4,X1_53) = X0_53
    | r2_hidden(X0_53,a_2_3_lattice3(sK4,X1_53)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4940])).

cnf(c_6905,plain,
    ( sK2(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),sK4,X1_53) = sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53))
    | r4_lattice3(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5422,c_5408])).

cnf(c_23,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_971,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_972,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_971])).

cnf(c_976,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X1)
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_972,c_30,c_29,c_27])).

cnf(c_977,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_976])).

cnf(c_4938,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_977])).

cnf(c_5410,plain,
    ( k15_lattice3(sK4,X0_54) = X0_53
    | r4_lattice3(sK4,X0_53,X0_54) != iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4938])).

cnf(c_14686,plain,
    ( sK2(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),sK4,X1_53) = sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53))
    | k15_lattice3(sK4,a_2_3_lattice3(sK4,X1_53)) = X0_53
    | r2_hidden(X0_53,a_2_3_lattice3(sK4,X1_53)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6905,c_5410])).

cnf(c_14758,plain,
    ( sK2(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK4,sK5) = sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5))
    | k15_lattice3(sK4,a_2_3_lattice3(sK4,sK5)) = sK5
    | r2_hidden(sK5,a_2_3_lattice3(sK4,sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14686])).

cnf(c_13,plain,
    ( r3_lattices(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_3_lattice3(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1040,plain,
    ( r3_lattices(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_3_lattice3(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_1041,plain,
    ( r3_lattices(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1040])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | r3_lattices(sK4,sK2(X0,sK4,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_30,c_29,c_27])).

cnf(c_1046,plain,
    ( r3_lattices(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1045])).

cnf(c_4935,plain,
    ( r3_lattices(sK4,sK2(X0_53,sK4,X1_53),X1_53)
    | ~ r2_hidden(X0_53,a_2_3_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1046])).

cnf(c_14276,plain,
    ( r3_lattices(sK4,sK2(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),sK4,X2_53),X2_53)
    | ~ r2_hidden(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),a_2_3_lattice3(sK4,X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4935])).

cnf(c_14278,plain,
    ( r3_lattices(sK4,sK2(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK4,sK5),sK5)
    | ~ r2_hidden(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),a_2_3_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_14276])).

cnf(c_5983,plain,
    ( ~ r3_lattices(sK4,X0_53,X1_53)
    | r3_lattices(sK4,sK1(sK4,X2_53,a_2_3_lattice3(sK4,X3_53)),X2_53)
    | X2_53 != X1_53
    | sK1(sK4,X2_53,a_2_3_lattice3(sK4,X3_53)) != X0_53 ),
    inference(instantiation,[status(thm)],[c_4957])).

cnf(c_8671,plain,
    ( ~ r3_lattices(sK4,sK2(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),sK4,X2_53),X3_53)
    | r3_lattices(sK4,sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),X0_53)
    | X0_53 != X3_53
    | sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)) != sK2(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_5983])).

cnf(c_8678,plain,
    ( ~ r3_lattices(sK4,sK2(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK4,sK5),sK5)
    | r3_lattices(sK4,sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK5)
    | sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)) != sK2(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK4,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_8671])).

cnf(c_6045,plain,
    ( X0_53 != X1_53
    | sK1(sK4,X2_53,a_2_3_lattice3(sK4,X3_53)) != X1_53
    | sK1(sK4,X2_53,a_2_3_lattice3(sK4,X3_53)) = X0_53 ),
    inference(instantiation,[status(thm)],[c_4952])).

cnf(c_6242,plain,
    ( X0_53 != sK1(sK4,X1_53,a_2_3_lattice3(sK4,X2_53))
    | sK1(sK4,X1_53,a_2_3_lattice3(sK4,X2_53)) = X0_53
    | sK1(sK4,X1_53,a_2_3_lattice3(sK4,X2_53)) != sK1(sK4,X1_53,a_2_3_lattice3(sK4,X2_53)) ),
    inference(instantiation,[status(thm)],[c_6045])).

cnf(c_6966,plain,
    ( sK2(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),sK4,X2_53) != sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53))
    | sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)) = sK2(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),sK4,X2_53)
    | sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)) != sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)) ),
    inference(instantiation,[status(thm)],[c_6242])).

cnf(c_6968,plain,
    ( sK2(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK4,sK5) != sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5))
    | sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)) = sK2(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK4,sK5)
    | sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)) != sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6966])).

cnf(c_5,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1350,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_30])).

cnf(c_1351,plain,
    ( r3_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1350])).

cnf(c_1355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_27])).

cnf(c_1356,plain,
    ( r3_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1355])).

cnf(c_4924,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1356])).

cnf(c_5426,plain,
    ( r3_lattice3(sK4,X0_53,X0_54) = iProver_top
    | r2_hidden(sK0(sK4,X0_53,X0_54),X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4924])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_884,plain,
    ( ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_885,plain,
    ( ~ r2_hidden(X0,a_2_4_lattice3(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | sK3(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_4_lattice3(sK4,X1))
    | sK3(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_885,c_30,c_29,c_27])).

cnf(c_890,plain,
    ( ~ r2_hidden(X0,a_2_4_lattice3(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | sK3(X0,sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_889])).

cnf(c_4942,plain,
    ( ~ r2_hidden(X0_53,a_2_4_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | sK3(X0_53,sK4,X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_890])).

cnf(c_5406,plain,
    ( sK3(X0_53,sK4,X1_53) = X0_53
    | r2_hidden(X0_53,a_2_4_lattice3(sK4,X1_53)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4942])).

cnf(c_6934,plain,
    ( sK3(sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)),sK4,X1_53) = sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53))
    | r3_lattice3(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5426,c_5406])).

cnf(c_6954,plain,
    ( r3_lattice3(sK4,X0_53,a_2_4_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | sK3(sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)),sK4,X1_53) = sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6934])).

cnf(c_6956,plain,
    ( r3_lattice3(sK4,sK5,a_2_4_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | sK3(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),sK4,sK5) = sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6954])).

cnf(c_4950,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_6892,plain,
    ( sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)) = sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)) ),
    inference(instantiation,[status(thm)],[c_4950])).

cnf(c_6895,plain,
    ( sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)) = sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6892])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_357,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_21])).

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

cnf(c_361,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_2,c_1])).

cnf(c_1153,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_361,c_29])).

cnf(c_1154,plain,
    ( ~ r3_lattices(sK4,X0,X1)
    | r1_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1153])).

cnf(c_1158,plain,
    ( ~ r3_lattices(sK4,X0,X1)
    | r1_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1154,c_30,c_27])).

cnf(c_4932,plain,
    ( ~ r3_lattices(sK4,X0_53,X1_53)
    | r1_lattices(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1158])).

cnf(c_6315,plain,
    ( ~ r3_lattices(sK4,X0_53,sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)))
    | r1_lattices(sK4,X0_53,sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4932])).

cnf(c_6317,plain,
    ( ~ r3_lattices(sK4,sK5,sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)))
    | r1_lattices(sK4,sK5,sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)))
    | ~ m1_subset_1(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6315])).

cnf(c_6041,plain,
    ( sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)) = sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)) ),
    inference(instantiation,[status(thm)],[c_4950])).

cnf(c_6044,plain,
    ( sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)) = sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6041])).

cnf(c_5887,plain,
    ( ~ r3_lattices(sK4,sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),X0_53)
    | r1_lattices(sK4,sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4932])).

cnf(c_5889,plain,
    ( ~ r3_lattices(sK4,sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK5)
    | r1_lattices(sK4,sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK5)
    | ~ m1_subset_1(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5887])).

cnf(c_5768,plain,
    ( r3_lattice3(sK4,X0_53,a_2_4_lattice3(sK4,X1_53))
    | r2_hidden(sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)),a_2_4_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4924])).

cnf(c_5780,plain,
    ( r3_lattice3(sK4,sK5,a_2_4_lattice3(sK4,sK5))
    | r2_hidden(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),a_2_4_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5768])).

cnf(c_4,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1371,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_30])).

cnf(c_1372,plain,
    ( ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1371])).

cnf(c_1376,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1372,c_27])).

cnf(c_1377,plain,
    ( ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1376])).

cnf(c_4923,plain,
    ( ~ r1_lattices(sK4,X0_53,sK0(sK4,X0_53,X0_54))
    | r3_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1377])).

cnf(c_5769,plain,
    ( ~ r1_lattices(sK4,X0_53,sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)))
    | r3_lattice3(sK4,X0_53,a_2_4_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4923])).

cnf(c_5776,plain,
    ( ~ r1_lattices(sK4,sK5,sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)))
    | r3_lattice3(sK4,sK5,a_2_4_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5769])).

cnf(c_6,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1329,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_1330,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1329])).

cnf(c_1334,plain,
    ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1330,c_27])).

cnf(c_1335,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1334])).

cnf(c_4925,plain,
    ( r3_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1335])).

cnf(c_5770,plain,
    ( r3_lattice3(sK4,X0_53,a_2_4_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_53,a_2_4_lattice3(sK4,X1_53)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4925])).

cnf(c_5772,plain,
    ( r3_lattice3(sK4,sK5,a_2_4_lattice3(sK4,sK5))
    | m1_subset_1(sK0(sK4,sK5,a_2_4_lattice3(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5770])).

cnf(c_5715,plain,
    ( r4_lattice3(sK4,X0_53,a_2_3_lattice3(sK4,X1_53))
    | r2_hidden(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),a_2_3_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4928])).

cnf(c_5727,plain,
    ( r4_lattice3(sK4,sK5,a_2_3_lattice3(sK4,sK5))
    | r2_hidden(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),a_2_3_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5715])).

cnf(c_8,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1281,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_1282,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1281])).

cnf(c_1286,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1282,c_27])).

cnf(c_1287,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1286])).

cnf(c_4927,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ r1_lattices(sK4,sK1(sK4,X0_53,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1287])).

cnf(c_5716,plain,
    ( r4_lattice3(sK4,X0_53,a_2_3_lattice3(sK4,X1_53))
    | ~ r1_lattices(sK4,sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4927])).

cnf(c_5723,plain,
    ( r4_lattice3(sK4,sK5,a_2_3_lattice3(sK4,sK5))
    | ~ r1_lattices(sK4,sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5716])).

cnf(c_10,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1239,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_1240,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1239])).

cnf(c_1244,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1240,c_27])).

cnf(c_1245,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1244])).

cnf(c_4929,plain,
    ( r4_lattice3(sK4,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_53,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1245])).

cnf(c_5717,plain,
    ( r4_lattice3(sK4,X0_53,a_2_3_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_53,a_2_3_lattice3(sK4,X1_53)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4929])).

cnf(c_5719,plain,
    ( r4_lattice3(sK4,sK5,a_2_3_lattice3(sK4,sK5))
    | m1_subset_1(sK1(sK4,sK5,a_2_3_lattice3(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5717])).

cnf(c_24,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_947,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_948,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_952,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X1)
    | ~ r3_lattice3(sK4,X0,X1)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_30,c_29,c_27])).

cnf(c_953,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_952])).

cnf(c_4939,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_953])).

cnf(c_5672,plain,
    ( ~ r3_lattice3(sK4,X0_53,a_2_4_lattice3(sK4,X1_53))
    | ~ r2_hidden(X0_53,a_2_4_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | k16_lattice3(sK4,a_2_4_lattice3(sK4,X1_53)) = X0_53 ),
    inference(instantiation,[status(thm)],[c_4939])).

cnf(c_5674,plain,
    ( ~ r3_lattice3(sK4,sK5,a_2_4_lattice3(sK4,sK5))
    | ~ r2_hidden(sK5,a_2_4_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k16_lattice3(sK4,a_2_4_lattice3(sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_5672])).

cnf(c_5642,plain,
    ( ~ r4_lattice3(sK4,X0_53,a_2_3_lattice3(sK4,X1_53))
    | ~ r2_hidden(X0_53,a_2_3_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_3_lattice3(sK4,X1_53)) = X0_53 ),
    inference(instantiation,[status(thm)],[c_4938])).

cnf(c_5644,plain,
    ( ~ r4_lattice3(sK4,sK5,a_2_3_lattice3(sK4,sK5))
    | ~ r2_hidden(sK5,a_2_3_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k15_lattice3(sK4,a_2_3_lattice3(sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_5642])).

cnf(c_22,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_328,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_22])).

cnf(c_332,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_2,c_1])).

cnf(c_1177,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_29])).

cnf(c_1178,plain,
    ( r3_lattices(sK4,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1177])).

cnf(c_1182,plain,
    ( r3_lattices(sK4,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1178,c_30,c_27])).

cnf(c_4931,plain,
    ( r3_lattices(sK4,X0_53,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1182])).

cnf(c_4946,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_4931])).

cnf(c_5013,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4946])).

cnf(c_5015,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_5013])).

cnf(c_5014,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_4946])).

cnf(c_4947,plain,
    ( r3_lattices(sK4,X0_53,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_4931])).

cnf(c_5010,plain,
    ( r3_lattices(sK4,X0_53,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4947])).

cnf(c_5012,plain,
    ( r3_lattices(sK4,sK5,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_5010])).

cnf(c_5011,plain,
    ( r3_lattices(sK4,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_4947])).

cnf(c_4948,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4931])).

cnf(c_5009,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4948])).

cnf(c_12,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r2_hidden(X1,a_2_3_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1061,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r2_hidden(X1,a_2_3_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_1062,plain,
    ( ~ r3_lattices(sK4,X0,X1)
    | r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_1066,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | ~ r3_lattices(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_30,c_29,c_27])).

cnf(c_1067,plain,
    ( ~ r3_lattices(sK4,X0,X1)
    | r2_hidden(X0,a_2_3_lattice3(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1066])).

cnf(c_4934,plain,
    ( ~ r3_lattices(sK4,X0_53,X1_53)
    | r2_hidden(X0_53,a_2_3_lattice3(sK4,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1067])).

cnf(c_5000,plain,
    ( r3_lattices(sK4,X0_53,X1_53) != iProver_top
    | r2_hidden(X0_53,a_2_3_lattice3(sK4,X1_53)) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4934])).

cnf(c_5002,plain,
    ( r3_lattices(sK4,sK5,sK5) != iProver_top
    | r2_hidden(sK5,a_2_3_lattice3(sK4,sK5)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5000])).

cnf(c_5001,plain,
    ( ~ r3_lattices(sK4,sK5,sK5)
    | r2_hidden(sK5,a_2_3_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4934])).

cnf(c_16,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r2_hidden(X2,a_2_4_lattice3(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1016,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r2_hidden(X2,a_2_4_lattice3(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_1017,plain,
    ( ~ r3_lattices(sK4,X0,X1)
    | r2_hidden(X1,a_2_4_lattice3(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,a_2_4_lattice3(sK4,X0))
    | ~ r3_lattices(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_30,c_29,c_27])).

cnf(c_1022,plain,
    ( ~ r3_lattices(sK4,X0,X1)
    | r2_hidden(X1,a_2_4_lattice3(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1021])).

cnf(c_4936,plain,
    ( ~ r3_lattices(sK4,X0_53,X1_53)
    | r2_hidden(X1_53,a_2_4_lattice3(sK4,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1022])).

cnf(c_4995,plain,
    ( ~ r3_lattices(sK4,sK5,sK5)
    | r2_hidden(sK5,a_2_4_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4936])).

cnf(c_25,negated_conjecture,
    ( k16_lattice3(sK4,a_2_4_lattice3(sK4,sK5)) != sK5
    | k15_lattice3(sK4,a_2_3_lattice3(sK4,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4945,negated_conjecture,
    ( k16_lattice3(sK4,a_2_4_lattice3(sK4,sK5)) != sK5
    | k15_lattice3(sK4,a_2_3_lattice3(sK4,sK5)) != sK5 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_4970,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_4950])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61762,c_22366,c_17094,c_14758,c_14278,c_8678,c_6968,c_6956,c_6895,c_6317,c_6044,c_5889,c_5780,c_5776,c_5772,c_5727,c_5723,c_5719,c_5674,c_5644,c_5015,c_5014,c_5012,c_5011,c_5009,c_4948,c_5002,c_5001,c_4995,c_4945,c_4970,c_35,c_26])).


%------------------------------------------------------------------------------

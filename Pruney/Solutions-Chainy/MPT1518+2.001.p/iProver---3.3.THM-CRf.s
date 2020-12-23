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
% DateTime   : Thu Dec  3 12:19:22 EST 2020

% Result     : Theorem 15.49s
% Output     : CNFRefutation 15.49s
% Verified   : 
% Statistics : Number of formulae       :  247 (1660 expanded)
%              Number of clauses        :  164 ( 376 expanded)
%              Number of leaves         :   20 ( 520 expanded)
%              Depth                    :   28
%              Number of atoms          : 1575 (15818 expanded)
%              Number of equality atoms :  118 (1545 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( l3_lattices(X0)
                  & v3_filter_0(X0)
                  & v10_lattices(X0)
                  & ~ v2_struct_0(X0) )
               => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) ) ) ) ) ),
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
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( l3_lattices(X0)
                    & v3_filter_0(X0)
                    & v10_lattices(X0)
                    & ~ v2_struct_0(X0) )
                 => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
              & l3_lattices(X0)
              & v3_filter_0(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
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
              ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
              & l3_lattices(X0)
              & v3_filter_0(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
          & l3_lattices(X0)
          & v3_filter_0(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k4_filter_0(X0,X1,sK6) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,sK6))
        & l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
              & l3_lattices(X0)
              & v3_filter_0(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k4_filter_0(X0,sK5,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,sK5,X2))
            & l3_lattices(X0)
            & v3_filter_0(X0)
            & v10_lattices(X0)
            & ~ v2_struct_0(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
                & l3_lattices(X0)
                & v3_filter_0(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k4_filter_0(sK4,X1,X2) != k15_lattice3(sK4,a_3_6_lattice3(sK4,X1,X2))
              & l3_lattices(sK4)
              & v3_filter_0(sK4)
              & v10_lattices(sK4)
              & ~ v2_struct_0(sK4)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k4_filter_0(sK4,sK5,sK6) != k15_lattice3(sK4,a_3_6_lattice3(sK4,sK5,sK6))
    & l3_lattices(sK4)
    & v3_filter_0(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f28,f50,f49,f48])).

fof(f79,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    k4_filter_0(sK4,sK5,sK6) != k15_lattice3(sK4,a_3_6_lattice3(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X1))
        & m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( r3_lattices(X1,k4_lattices(X1,X2,X5),X3)
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r3_lattices(X1,k4_lattices(X1,X2,X5),X3)
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r3_lattices(X1,k4_lattices(X1,X2,sK3(X0,X1,X2,X3)),X3)
        & sK3(X0,X1,X2,X3) = X0
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,k4_lattices(X1,X2,sK3(X0,X1,X2,X3)),X3)
            & sK3(X0,X1,X2,X3) = X0
            & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
      | X0 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,a_3_6_lattice3(X1,X2,X3))
      | ~ r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( l3_lattices(X0)
                  & v3_filter_0(X0)
                  & v10_lattices(X0)
                  & ~ v2_struct_0(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k4_filter_0(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                             => r3_lattices(X0,X4,X3) ) )
                        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_filter_0(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r3_lattices(X0,X4,X3)
                          | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_filter_0(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r3_lattices(X0,X4,X3)
                          | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_filter_0(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r3_lattices(X0,X4,X3)
                          & r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
                    & ( ( ! [X4] :
                            ( r3_lattices(X0,X4,X3)
                            | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
                      | k4_filter_0(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_filter_0(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r3_lattices(X0,X4,X3)
                          & r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
                    & ( ( ! [X4] :
                            ( r3_lattices(X0,X4,X3)
                            | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
                      | k4_filter_0(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_filter_0(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r3_lattices(X0,X4,X3)
                          & r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
                    & ( ( ! [X5] :
                            ( r3_lattices(X0,X5,X3)
                            | ~ r3_lattices(X0,k4_lattices(X0,X1,X5),X2)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
                      | k4_filter_0(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r3_lattices(X0,X4,X3)
          & r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK0(X0,X1,X2,X3),X3)
        & r3_lattices(X0,k4_lattices(X0,X1,sK0(X0,X1,X2,X3)),X2)
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_filter_0(X0,X1,X2) = X3
                      | ( ~ r3_lattices(X0,sK0(X0,X1,X2,X3),X3)
                        & r3_lattices(X0,k4_lattices(X0,X1,sK0(X0,X1,X2,X3)),X2)
                        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
                    & ( ( ! [X5] :
                            ( r3_lattices(X0,X5,X3)
                            | ~ r3_lattices(X0,k4_lattices(X0,X1,X5),X2)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
                      | k4_filter_0(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X0,k4_lattices(X0,X1,X3),X2)
      | k4_filter_0(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
      | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f85,plain,(
    v3_filter_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sK3(X0,X1,X2,X3) = X0
      | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f55,plain,(
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

fof(f57,plain,(
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

fof(f53,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r3_lattices(X0,X5,X3)
      | ~ r3_lattices(X0,k4_lattices(X0,X1,X5),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k4_filter_0(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X2,X0,X5,X1] :
      ( r3_lattices(X0,X5,k4_filter_0(X0,X1,X2))
      | ~ r3_lattices(X0,k4_lattices(X0,X1,X5),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X1,k4_lattices(X1,X2,sK3(X0,X1,X2,X3)),X3)
      | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_715,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_716,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_720,plain,
    ( m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_35,c_34,c_32])).

cnf(c_721,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_720])).

cnf(c_2110,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0_55,X0_54),u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_55) = X0_54 ),
    inference(subtyping,[status(esa)],[c_721])).

cnf(c_17,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_739,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_740,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_35,c_34,c_32])).

cnf(c_745,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_744])).

cnf(c_2109,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | r4_lattice3(sK4,sK2(sK4,X0_55,X0_54),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_55) = X0_54 ),
    inference(subtyping,[status(esa)],[c_745])).

cnf(c_15,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_970,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_971,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_970])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_971,c_32])).

cnf(c_976,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_975])).

cnf(c_2100,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | r1_lattices(sK4,X1_54,X0_54)
    | ~ r2_hidden(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_976])).

cnf(c_37144,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | r1_lattices(sK4,X1_54,sK2(sK4,X0_55,X0_54))
    | ~ r2_hidden(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,X0_55,X0_54),u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_55) = X0_54 ),
    inference(resolution,[status(thm)],[c_2109,c_2100])).

cnf(c_37156,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | r1_lattices(sK4,X1_54,sK2(sK4,X0_55,X0_54))
    | ~ r2_hidden(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_55) = X0_54 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2110,c_37144])).

cnf(c_16,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_763,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_764,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ r4_lattice3(sK4,X0,X1)
    | k15_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_35,c_34,c_32])).

cnf(c_769,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k15_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_768])).

cnf(c_2108,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | ~ r1_lattices(sK4,X0_54,sK2(sK4,X0_55,X0_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_55) = X0_54 ),
    inference(subtyping,[status(esa)],[c_769])).

cnf(c_37240,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | ~ r2_hidden(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | k15_lattice3(sK4,X0_55) = X0_54 ),
    inference(resolution,[status(thm)],[c_37156,c_2108])).

cnf(c_2124,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_2122,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3084,plain,
    ( X0_54 != X1_54
    | X1_54 = X0_54 ),
    inference(resolution,[status(thm)],[c_2124,c_2122])).

cnf(c_37598,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | ~ r2_hidden(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | X0_54 = k15_lattice3(sK4,X0_55) ),
    inference(resolution,[status(thm)],[c_37240,c_3084])).

cnf(c_25,negated_conjecture,
    ( k4_filter_0(sK4,sK5,sK6) != k15_lattice3(sK4,a_3_6_lattice3(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2120,negated_conjecture,
    ( k4_filter_0(sK4,sK5,sK6) != k15_lattice3(sK4,a_3_6_lattice3(sK4,sK5,sK6)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_41306,plain,
    ( ~ r4_lattice3(sK4,k4_filter_0(sK4,sK5,sK6),a_3_6_lattice3(sK4,sK5,sK6))
    | ~ r2_hidden(k4_filter_0(sK4,sK5,sK6),a_3_6_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(k4_filter_0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_37598,c_2120])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ r3_lattices(X0,k4_lattices(X0,X1,X2),X3)
    | r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_646,plain,
    ( ~ r3_lattices(X0,k4_lattices(X0,X1,X2),X3)
    | r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_647,plain,
    ( ~ r3_lattices(sK4,k4_lattices(sK4,X0,X1),X2)
    | r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
    | ~ r3_lattices(sK4,k4_lattices(sK4,X0,X1),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_35,c_34,c_32])).

cnf(c_652,plain,
    ( ~ r3_lattices(sK4,k4_lattices(sK4,X0,X1),X2)
    | r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_651])).

cnf(c_2113,plain,
    ( ~ r3_lattices(sK4,k4_lattices(sK4,X0_54,X1_54),X2_54)
    | r2_hidden(X1_54,a_3_6_lattice3(sK4,X0_54,X2_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_652])).

cnf(c_2747,plain,
    ( ~ r3_lattices(sK4,k4_lattices(sK4,X0_54,k4_filter_0(sK4,X0_54,X1_54)),X1_54)
    | r2_hidden(k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_filter_0(sK4,X0_54,X1_54),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2113])).

cnf(c_5454,plain,
    ( ~ r3_lattices(sK4,k4_lattices(sK4,sK5,k4_filter_0(sK4,sK5,sK6)),sK6)
    | r2_hidden(k4_filter_0(sK4,sK5,sK6),a_3_6_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(k4_filter_0(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2747])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_filter_0(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_filter_0(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_932,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_928,c_35,c_32])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k4_filter_0(sK4,X1,X0),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_932])).

cnf(c_2103,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | m1_subset_1(k4_filter_0(sK4,X1_54,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_933])).

cnf(c_8894,plain,
    ( m1_subset_1(k4_filter_0(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2103])).

cnf(c_10,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
    | ~ v3_filter_0(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_27,negated_conjecture,
    ( v3_filter_0(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_445,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_446,plain,
    ( r3_lattices(sK4,k4_lattices(sK4,X0,k4_filter_0(sK4,X0,X1)),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_450,plain,
    ( ~ m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattices(sK4,k4_lattices(sK4,X0,k4_filter_0(sK4,X0,X1)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_35,c_34,c_32])).

cnf(c_451,plain,
    ( r3_lattices(sK4,k4_lattices(sK4,X0,k4_filter_0(sK4,X0,X1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_450])).

cnf(c_961,plain,
    ( r3_lattices(sK4,k4_lattices(sK4,X0,k4_filter_0(sK4,X0,X1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_933,c_451])).

cnf(c_2102,plain,
    ( r3_lattices(sK4,k4_lattices(sK4,X0_54,k4_filter_0(sK4,X0_54,X1_54)),X1_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_961])).

cnf(c_15538,plain,
    ( r3_lattices(sK4,k4_lattices(sK4,sK5,k4_filter_0(sK4,sK5,sK6)),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2102])).

cnf(c_41449,plain,
    ( ~ r4_lattice3(sK4,k4_filter_0(sK4,sK5,sK6),a_3_6_lattice3(sK4,sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41306,c_31,c_30,c_5454,c_8894,c_15538])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3(X0,X1,X2,X3) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_811,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3(X0,X1,X2,X3) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_812,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | sK3(X0,sK4,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
    | sK3(X0,sK4,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_35,c_34,c_32])).

cnf(c_817,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | sK3(X0,sK4,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_816])).

cnf(c_2106,plain,
    ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | sK3(X0_54,sK4,X1_54,X2_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_817])).

cnf(c_4962,plain,
    ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | X0_54 = sK3(X0_54,sK4,X1_54,X2_54) ),
    inference(resolution,[status(thm)],[c_3084,c_2106])).

cnf(c_2125,plain,
    ( ~ r3_lattices(X0_53,X0_54,X1_54)
    | r3_lattices(X0_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_5099,plain,
    ( r3_lattices(X0_53,X0_54,X1_54)
    | ~ r3_lattices(X0_53,X2_54,sK3(X1_54,sK4,X3_54,X4_54))
    | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X3_54,X4_54))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X4_54,u1_struct_0(sK4))
    | X0_54 != X2_54 ),
    inference(resolution,[status(thm)],[c_4962,c_2125])).

cnf(c_2126,plain,
    ( ~ r1_lattices(X0_53,X0_54,X1_54)
    | r1_lattices(X0_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3951,plain,
    ( ~ r1_lattices(X0_53,X0_54,X1_54)
    | r1_lattices(X0_53,X2_54,sK3(X1_54,sK4,X3_54,X4_54))
    | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X3_54,X4_54))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X4_54,u1_struct_0(sK4))
    | X2_54 != X0_54 ),
    inference(resolution,[status(thm)],[c_2126,c_2106])).

cnf(c_4298,plain,
    ( ~ r1_lattices(X0_53,X0_54,X1_54)
    | r1_lattices(X0_53,X0_54,sK3(X1_54,sK4,X2_54,X3_54))
    | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X2_54,X3_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_3951,c_2122])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_397,plain,
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
    inference(cnf_transformation,[],[f53])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_401,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_2,c_1])).

cnf(c_879,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_28])).

cnf(c_880,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_884,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_880,c_35,c_32])).

cnf(c_885,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_884])).

cnf(c_2105,plain,
    ( ~ r1_lattices(sK4,X0_54,X1_54)
    | r3_lattices(sK4,X0_54,X1_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_885])).

cnf(c_6700,plain,
    ( ~ r1_lattices(sK4,X0_54,X1_54)
    | r3_lattices(sK4,X0_54,sK3(X1_54,sK4,X2_54,X3_54))
    | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X2_54,X3_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(X1_54,sK4,X2_54,X3_54),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_4298,c_2105])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_787,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_788,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | m1_subset_1(sK3(X0,sK4,X1,X2),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_792,plain,
    ( m1_subset_1(sK3(X0,sK4,X1,X2),u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_788,c_35,c_34,c_32])).

cnf(c_793,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | m1_subset_1(sK3(X0,sK4,X1,X2),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_792])).

cnf(c_2107,plain,
    ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | m1_subset_1(sK3(X0_54,sK4,X1_54,X2_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_793])).

cnf(c_6791,plain,
    ( ~ r1_lattices(sK4,X0_54,X1_54)
    | r3_lattices(sK4,X0_54,sK3(X1_54,sK4,X2_54,X3_54))
    | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X2_54,X3_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6700,c_2107])).

cnf(c_25083,plain,
    ( ~ r1_lattices(sK4,X0_54,X1_54)
    | r3_lattices(sK4,X2_54,X1_54)
    | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X3_54,X4_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X4_54,u1_struct_0(sK4))
    | X2_54 != X0_54 ),
    inference(resolution,[status(thm)],[c_5099,c_6791])).

cnf(c_3610,plain,
    ( r2_hidden(k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_filter_0(sK4,X0_54,X1_54),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_2102,c_2113])).

cnf(c_3708,plain,
    ( r2_hidden(k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3610,c_2103])).

cnf(c_35358,plain,
    ( ~ r1_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
    | r3_lattices(sK4,X3_54,k4_filter_0(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | X3_54 != X0_54 ),
    inference(resolution,[status(thm)],[c_25083,c_3708])).

cnf(c_3955,plain,
    ( ~ r1_lattices(X0_53,X0_54,X1_54)
    | r1_lattices(X0_53,X2_54,X1_54)
    | X2_54 != X0_54 ),
    inference(resolution,[status(thm)],[c_2126,c_2122])).

cnf(c_5782,plain,
    ( r1_lattices(X0_53,X0_54,X1_54)
    | ~ r1_lattices(X0_53,sK3(X0_54,sK4,X2_54,X3_54),X1_54)
    | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X2_54,X3_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_3955,c_4962])).

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
    inference(cnf_transformation,[],[f56])).

cnf(c_365,plain,
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

cnf(c_369,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_2,c_1])).

cnf(c_903,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_369,c_28])).

cnf(c_904,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_908,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_904,c_35,c_32])).

cnf(c_909,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_908])).

cnf(c_2104,plain,
    ( r1_lattices(sK4,X0_54,X1_54)
    | ~ r3_lattices(sK4,X0_54,X1_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_909])).

cnf(c_11159,plain,
    ( r1_lattices(sK4,X0_54,X1_54)
    | ~ r3_lattices(sK4,sK3(X0_54,sK4,X2_54,X3_54),X1_54)
    | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X2_54,X3_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(X0_54,sK4,X2_54,X3_54),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_5782,c_2104])).

cnf(c_11175,plain,
    ( r1_lattices(sK4,X0_54,X1_54)
    | ~ r3_lattices(sK4,sK3(X0_54,sK4,X2_54,X3_54),X1_54)
    | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X2_54,X3_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11159,c_2107])).

cnf(c_9,plain,
    ( r3_lattices(X0,X1,k4_filter_0(X0,X2,X3))
    | ~ r3_lattices(X0,k4_lattices(X0,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k4_filter_0(X0,X2,X3),u1_struct_0(X0))
    | ~ v3_filter_0(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_469,plain,
    ( r3_lattices(X0,X1,k4_filter_0(X0,X2,X3))
    | ~ r3_lattices(X0,k4_lattices(X0,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k4_filter_0(X0,X2,X3),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_470,plain,
    ( r3_lattices(sK4,X0,k4_filter_0(sK4,X1,X2))
    | ~ r3_lattices(sK4,k4_lattices(sK4,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_filter_0(sK4,X1,X2),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_474,plain,
    ( ~ m1_subset_1(k4_filter_0(sK4,X1,X2),u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r3_lattices(sK4,k4_lattices(sK4,X1,X0),X2)
    | r3_lattices(sK4,X0,k4_filter_0(sK4,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_35,c_34,c_32])).

cnf(c_475,plain,
    ( r3_lattices(sK4,X0,k4_filter_0(sK4,X1,X2))
    | ~ r3_lattices(sK4,k4_lattices(sK4,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_filter_0(sK4,X1,X2),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_474])).

cnf(c_962,plain,
    ( r3_lattices(sK4,X0,k4_filter_0(sK4,X1,X2))
    | ~ r3_lattices(sK4,k4_lattices(sK4,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_933,c_475])).

cnf(c_2101,plain,
    ( r3_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
    | ~ r3_lattices(sK4,k4_lattices(sK4,X1_54,X0_54),X2_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_962])).

cnf(c_22,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,sK3(X2,X0,X1,X3)),X3)
    | ~ r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_622,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,sK3(X2,X0,X1,X3)),X3)
    | ~ r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_623,plain,
    ( r3_lattices(sK4,k4_lattices(sK4,X0,sK3(X1,sK4,X0,X2)),X2)
    | ~ r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
    | r3_lattices(sK4,k4_lattices(sK4,X0,sK3(X1,sK4,X0,X2)),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_35,c_34,c_32])).

cnf(c_628,plain,
    ( r3_lattices(sK4,k4_lattices(sK4,X0,sK3(X1,sK4,X0,X2)),X2)
    | ~ r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_627])).

cnf(c_2114,plain,
    ( r3_lattices(sK4,k4_lattices(sK4,X0_54,sK3(X1_54,sK4,X0_54,X2_54)),X2_54)
    | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X0_54,X2_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_628])).

cnf(c_4092,plain,
    ( r3_lattices(sK4,sK3(X0_54,sK4,X1_54,X2_54),k4_filter_0(sK4,X1_54,X2_54))
    | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(X0_54,sK4,X1_54,X2_54),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_2101,c_2114])).

cnf(c_4489,plain,
    ( ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | r3_lattices(sK4,sK3(X0_54,sK4,X1_54,X2_54),k4_filter_0(sK4,X1_54,X2_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4092,c_2107])).

cnf(c_4490,plain,
    ( r3_lattices(sK4,sK3(X0_54,sK4,X1_54,X2_54),k4_filter_0(sK4,X1_54,X2_54))
    | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_4489])).

cnf(c_11204,plain,
    ( r1_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
    | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_filter_0(sK4,X1_54,X2_54),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_11175,c_4490])).

cnf(c_15706,plain,
    ( r1_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
    | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11204,c_2103])).

cnf(c_35525,plain,
    ( r3_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
    | ~ r2_hidden(X3_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
    | X0_54 != X3_54 ),
    inference(resolution,[status(thm)],[c_35358,c_15706])).

cnf(c_2127,plain,
    ( ~ m1_subset_1(X0_54,X0_56)
    | m1_subset_1(X1_54,X0_56)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_5107,plain,
    ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | m1_subset_1(X0_54,X0_56)
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(X0_54,sK4,X1_54,X2_54),X0_56) ),
    inference(resolution,[status(thm)],[c_4962,c_2127])).

cnf(c_5523,plain,
    ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_5107,c_2107])).

cnf(c_35541,plain,
    ( r3_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
    | ~ r2_hidden(X3_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | X0_54 != X3_54 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_35525,c_5523])).

cnf(c_13,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1018,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_1019,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1018])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1019,c_32])).

cnf(c_1024,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1023])).

cnf(c_2098,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | r2_hidden(sK1(sK4,X0_54,X0_55),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1024])).

cnf(c_35684,plain,
    ( r4_lattice3(sK4,X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | r3_lattices(sK4,X3_54,k4_filter_0(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | X3_54 != sK1(sK4,X0_54,a_3_6_lattice3(sK4,X1_54,X2_54)) ),
    inference(resolution,[status(thm)],[c_35541,c_2098])).

cnf(c_35742,plain,
    ( r4_lattice3(sK4,X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
    | r3_lattices(sK4,sK1(sK4,X0_54,a_3_6_lattice3(sK4,X1_54,X2_54)),k4_filter_0(sK4,X1_54,X2_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_35684,c_2122])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1039,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_1040,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1039])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1040,c_32])).

cnf(c_1045,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1044])).

cnf(c_2097,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ r1_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1045])).

cnf(c_3337,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_2097,c_2104])).

cnf(c_14,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_997,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_998,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_997])).

cnf(c_1002,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_998,c_32])).

cnf(c_1003,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1002])).

cnf(c_2099,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1003])).

cnf(c_3615,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
    | r4_lattice3(sK4,X0_54,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3337,c_2099])).

cnf(c_3616,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_3615])).

cnf(c_36834,plain,
    ( r4_lattice3(sK4,k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_filter_0(sK4,X0_54,X1_54),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_35742,c_3616])).

cnf(c_36978,plain,
    ( r4_lattice3(sK4,k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_36834,c_2103])).

cnf(c_41461,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_41449,c_36978])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41461,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.49/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.49/2.51  
% 15.49/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.49/2.51  
% 15.49/2.51  ------  iProver source info
% 15.49/2.51  
% 15.49/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.49/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.49/2.51  git: non_committed_changes: false
% 15.49/2.51  git: last_make_outside_of_git: false
% 15.49/2.51  
% 15.49/2.51  ------ 
% 15.49/2.51  ------ Parsing...
% 15.49/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.49/2.51  
% 15.49/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 15.49/2.51  
% 15.49/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.49/2.51  
% 15.49/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.49/2.51  ------ Proving...
% 15.49/2.51  ------ Problem Properties 
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  clauses                                 24
% 15.49/2.51  conjectures                             3
% 15.49/2.51  EPR                                     0
% 15.49/2.51  Horn                                    18
% 15.49/2.51  unary                                   3
% 15.49/2.51  binary                                  1
% 15.49/2.51  lits                                    89
% 15.49/2.51  lits eq                                 8
% 15.49/2.51  fd_pure                                 0
% 15.49/2.51  fd_pseudo                               0
% 15.49/2.51  fd_cond                                 0
% 15.49/2.51  fd_pseudo_cond                          6
% 15.49/2.51  AC symbols                              0
% 15.49/2.51  
% 15.49/2.51  ------ Input Options Time Limit: Unbounded
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  ------ 
% 15.49/2.51  Current options:
% 15.49/2.51  ------ 
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  ------ Proving...
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  % SZS status Theorem for theBenchmark.p
% 15.49/2.51  
% 15.49/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.49/2.51  
% 15.49/2.51  fof(f6,axiom,(
% 15.49/2.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f23,plain,(
% 15.49/2.51    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f6])).
% 15.49/2.51  
% 15.49/2.51  fof(f24,plain,(
% 15.49/2.51    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(flattening,[],[f23])).
% 15.49/2.51  
% 15.49/2.51  fof(f39,plain,(
% 15.49/2.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(nnf_transformation,[],[f24])).
% 15.49/2.51  
% 15.49/2.51  fof(f40,plain,(
% 15.49/2.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(flattening,[],[f39])).
% 15.49/2.51  
% 15.49/2.51  fof(f41,plain,(
% 15.49/2.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(rectify,[],[f40])).
% 15.49/2.51  
% 15.49/2.51  fof(f42,plain,(
% 15.49/2.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f43,plain,(
% 15.49/2.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 15.49/2.51  
% 15.49/2.51  fof(f70,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f43])).
% 15.49/2.51  
% 15.49/2.51  fof(f8,conjecture,(
% 15.49/2.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f9,negated_conjecture,(
% 15.49/2.51    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))))))),
% 15.49/2.51    inference(negated_conjecture,[],[f8])).
% 15.49/2.51  
% 15.49/2.51  fof(f27,plain,(
% 15.49/2.51    ? [X0] : (? [X1] : (? [X2] : ((k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & (l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f9])).
% 15.49/2.51  
% 15.49/2.51  fof(f28,plain,(
% 15.49/2.51    ? [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 15.49/2.51    inference(flattening,[],[f27])).
% 15.49/2.51  
% 15.49/2.51  fof(f50,plain,(
% 15.49/2.51    ( ! [X0,X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) => (k4_filter_0(X0,X1,sK6) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,sK6)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f49,plain,(
% 15.49/2.51    ( ! [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k4_filter_0(X0,sK5,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,sK5,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f48,plain,(
% 15.49/2.51    ? [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k4_filter_0(sK4,X1,X2) != k15_lattice3(sK4,a_3_6_lattice3(sK4,X1,X2)) & l3_lattices(sK4) & v3_filter_0(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f51,plain,(
% 15.49/2.51    ((k4_filter_0(sK4,sK5,sK6) != k15_lattice3(sK4,a_3_6_lattice3(sK4,sK5,sK6)) & l3_lattices(sK4) & v3_filter_0(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 15.49/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f28,f50,f49,f48])).
% 15.49/2.51  
% 15.49/2.51  fof(f79,plain,(
% 15.49/2.51    v4_lattice3(sK4)),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f77,plain,(
% 15.49/2.51    ~v2_struct_0(sK4)),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f78,plain,(
% 15.49/2.51    v10_lattices(sK4)),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f80,plain,(
% 15.49/2.51    l3_lattices(sK4)),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f71,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK2(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f43])).
% 15.49/2.51  
% 15.49/2.51  fof(f5,axiom,(
% 15.49/2.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f21,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f5])).
% 15.49/2.51  
% 15.49/2.51  fof(f22,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(flattening,[],[f21])).
% 15.49/2.51  
% 15.49/2.51  fof(f35,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(nnf_transformation,[],[f22])).
% 15.49/2.51  
% 15.49/2.51  fof(f36,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(rectify,[],[f35])).
% 15.49/2.51  
% 15.49/2.51  fof(f37,plain,(
% 15.49/2.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f38,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 15.49/2.51  
% 15.49/2.51  fof(f64,plain,(
% 15.49/2.51    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f38])).
% 15.49/2.51  
% 15.49/2.51  fof(f83,plain,(
% 15.49/2.51    ~v2_struct_0(sK4)),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f72,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK2(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f43])).
% 15.49/2.51  
% 15.49/2.51  fof(f87,plain,(
% 15.49/2.51    k4_filter_0(sK4,sK5,sK6) != k15_lattice3(sK4,a_3_6_lattice3(sK4,sK5,sK6))),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f81,plain,(
% 15.49/2.51    m1_subset_1(sK5,u1_struct_0(sK4))),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f82,plain,(
% 15.49/2.51    m1_subset_1(sK6,u1_struct_0(sK4))),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f7,axiom,(
% 15.49/2.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f25,plain,(
% 15.49/2.51    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))) | (~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 15.49/2.51    inference(ennf_transformation,[],[f7])).
% 15.49/2.51  
% 15.49/2.51  fof(f26,plain,(
% 15.49/2.51    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 15.49/2.51    inference(flattening,[],[f25])).
% 15.49/2.51  
% 15.49/2.51  fof(f44,plain,(
% 15.49/2.51    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ! [X4] : (~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 15.49/2.51    inference(nnf_transformation,[],[f26])).
% 15.49/2.51  
% 15.49/2.51  fof(f45,plain,(
% 15.49/2.51    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ! [X4] : (~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X5] : (r3_lattices(X1,k4_lattices(X1,X2,X5),X3) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 15.49/2.51    inference(rectify,[],[f44])).
% 15.49/2.51  
% 15.49/2.51  fof(f46,plain,(
% 15.49/2.51    ! [X3,X2,X1,X0] : (? [X5] : (r3_lattices(X1,k4_lattices(X1,X2,X5),X3) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (r3_lattices(X1,k4_lattices(X1,X2,sK3(X0,X1,X2,X3)),X3) & sK3(X0,X1,X2,X3) = X0 & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))))),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f47,plain,(
% 15.49/2.51    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ! [X4] : (~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)))) & ((r3_lattices(X1,k4_lattices(X1,X2,sK3(X0,X1,X2,X3)),X3) & sK3(X0,X1,X2,X3) = X0 & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 15.49/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 15.49/2.51  
% 15.49/2.51  fof(f76,plain,(
% 15.49/2.51    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f47])).
% 15.49/2.51  
% 15.49/2.51  fof(f92,plain,(
% 15.49/2.51    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,a_3_6_lattice3(X1,X2,X3)) | ~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 15.49/2.51    inference(equality_resolution,[],[f76])).
% 15.49/2.51  
% 15.49/2.51  fof(f4,axiom,(
% 15.49/2.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f19,plain,(
% 15.49/2.51    ! [X0,X1,X2] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f4])).
% 15.49/2.51  
% 15.49/2.51  fof(f20,plain,(
% 15.49/2.51    ! [X0,X1,X2] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(flattening,[],[f19])).
% 15.49/2.51  
% 15.49/2.51  fof(f63,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f20])).
% 15.49/2.51  
% 15.49/2.51  fof(f84,plain,(
% 15.49/2.51    v10_lattices(sK4)),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f3,axiom,(
% 15.49/2.51    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_lattices(X0,k4_lattices(X0,X1,X4),X2) => r3_lattices(X0,X4,X3))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))))))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f17,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : ((r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f3])).
% 15.49/2.51  
% 15.49/2.51  fof(f18,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(flattening,[],[f17])).
% 15.49/2.51  
% 15.49/2.51  fof(f30,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_filter_0(X0,X1,X2) = X3 | (? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) & ((! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | k4_filter_0(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(nnf_transformation,[],[f18])).
% 15.49/2.51  
% 15.49/2.51  fof(f31,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_filter_0(X0,X1,X2) = X3 | ? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) & ((! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | k4_filter_0(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(flattening,[],[f30])).
% 15.49/2.51  
% 15.49/2.51  fof(f32,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_filter_0(X0,X1,X2) = X3 | ? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) & ((! [X5] : (r3_lattices(X0,X5,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | k4_filter_0(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(rectify,[],[f31])).
% 15.49/2.51  
% 15.49/2.51  fof(f33,plain,(
% 15.49/2.51    ! [X3,X2,X1,X0] : (? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0))) => (~r3_lattices(X0,sK0(X0,X1,X2,X3),X3) & r3_lattices(X0,k4_lattices(X0,X1,sK0(X0,X1,X2,X3)),X2) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f34,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_filter_0(X0,X1,X2) = X3 | (~r3_lattices(X0,sK0(X0,X1,X2,X3),X3) & r3_lattices(X0,k4_lattices(X0,X1,sK0(X0,X1,X2,X3)),X2) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) & ((! [X5] : (r3_lattices(X0,X5,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | k4_filter_0(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 15.49/2.51  
% 15.49/2.51  fof(f58,plain,(
% 15.49/2.51    ( ! [X2,X0,X3,X1] : (r3_lattices(X0,k4_lattices(X0,X1,X3),X2) | k4_filter_0(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f34])).
% 15.49/2.51  
% 15.49/2.51  fof(f89,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2) | ~m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(equality_resolution,[],[f58])).
% 15.49/2.51  
% 15.49/2.51  fof(f85,plain,(
% 15.49/2.51    v3_filter_0(sK4)),
% 15.49/2.51    inference(cnf_transformation,[],[f51])).
% 15.49/2.51  
% 15.49/2.51  fof(f74,plain,(
% 15.49/2.51    ( ! [X2,X0,X3,X1] : (sK3(X0,X1,X2,X3) = X0 | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f47])).
% 15.49/2.51  
% 15.49/2.51  fof(f1,axiom,(
% 15.49/2.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f10,plain,(
% 15.49/2.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.49/2.51    inference(pure_predicate_removal,[],[f1])).
% 15.49/2.51  
% 15.49/2.51  fof(f11,plain,(
% 15.49/2.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.49/2.51    inference(pure_predicate_removal,[],[f10])).
% 15.49/2.51  
% 15.49/2.51  fof(f12,plain,(
% 15.49/2.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 15.49/2.51    inference(pure_predicate_removal,[],[f11])).
% 15.49/2.51  
% 15.49/2.51  fof(f13,plain,(
% 15.49/2.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 15.49/2.51    inference(ennf_transformation,[],[f12])).
% 15.49/2.51  
% 15.49/2.51  fof(f14,plain,(
% 15.49/2.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 15.49/2.51    inference(flattening,[],[f13])).
% 15.49/2.51  
% 15.49/2.51  fof(f55,plain,(
% 15.49/2.51    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f14])).
% 15.49/2.51  
% 15.49/2.51  fof(f2,axiom,(
% 15.49/2.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f15,plain,(
% 15.49/2.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f2])).
% 15.49/2.51  
% 15.49/2.51  fof(f16,plain,(
% 15.49/2.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(flattening,[],[f15])).
% 15.49/2.51  
% 15.49/2.51  fof(f29,plain,(
% 15.49/2.51    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 15.49/2.51    inference(nnf_transformation,[],[f16])).
% 15.49/2.51  
% 15.49/2.51  fof(f57,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f29])).
% 15.49/2.51  
% 15.49/2.51  fof(f53,plain,(
% 15.49/2.51    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f14])).
% 15.49/2.51  
% 15.49/2.51  fof(f54,plain,(
% 15.49/2.51    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f14])).
% 15.49/2.51  
% 15.49/2.51  fof(f73,plain,(
% 15.49/2.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f47])).
% 15.49/2.51  
% 15.49/2.51  fof(f56,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f29])).
% 15.49/2.51  
% 15.49/2.51  fof(f59,plain,(
% 15.49/2.51    ( ! [X2,X0,X5,X3,X1] : (r3_lattices(X0,X5,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X0)) | k4_filter_0(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f34])).
% 15.49/2.51  
% 15.49/2.51  fof(f88,plain,(
% 15.49/2.51    ( ! [X2,X0,X5,X1] : (r3_lattices(X0,X5,k4_filter_0(X0,X1,X2)) | ~r3_lattices(X0,k4_lattices(X0,X1,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(equality_resolution,[],[f59])).
% 15.49/2.51  
% 15.49/2.51  fof(f75,plain,(
% 15.49/2.51    ( ! [X2,X0,X3,X1] : (r3_lattices(X1,k4_lattices(X1,X2,sK3(X0,X1,X2,X3)),X3) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f47])).
% 15.49/2.51  
% 15.49/2.51  fof(f66,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f38])).
% 15.49/2.51  
% 15.49/2.51  fof(f67,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f38])).
% 15.49/2.51  
% 15.49/2.51  fof(f65,plain,(
% 15.49/2.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f38])).
% 15.49/2.51  
% 15.49/2.51  cnf(c_18,plain,
% 15.49/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 15.49/2.51      | ~ v4_lattice3(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | k15_lattice3(X0,X2) = X1 ),
% 15.49/2.51      inference(cnf_transformation,[],[f70]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_33,negated_conjecture,
% 15.49/2.51      ( v4_lattice3(sK4) ),
% 15.49/2.51      inference(cnf_transformation,[],[f79]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_715,plain,
% 15.49/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | k15_lattice3(X0,X2) = X1
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_716,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4)
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_715]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_35,negated_conjecture,
% 15.49/2.51      ( ~ v2_struct_0(sK4) ),
% 15.49/2.51      inference(cnf_transformation,[],[f77]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_34,negated_conjecture,
% 15.49/2.51      ( v10_lattices(sK4) ),
% 15.49/2.51      inference(cnf_transformation,[],[f78]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_32,negated_conjecture,
% 15.49/2.51      ( l3_lattices(sK4) ),
% 15.49/2.51      inference(cnf_transformation,[],[f80]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_720,plain,
% 15.49/2.51      ( m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_716,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_721,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_720]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2110,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK2(sK4,X0_55,X0_54),u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X0_55) = X0_54 ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_721]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_17,plain,
% 15.49/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.49/2.51      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ v4_lattice3(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | k15_lattice3(X0,X2) = X1 ),
% 15.49/2.51      inference(cnf_transformation,[],[f71]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_739,plain,
% 15.49/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.49/2.51      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | k15_lattice3(X0,X2) = X1
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_740,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4)
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_739]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_744,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 15.49/2.51      | ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_740,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_745,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | r4_lattice3(sK4,sK2(sK4,X1,X0),X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_744]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2109,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | r4_lattice3(sK4,sK2(sK4,X0_55,X0_54),X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X0_55) = X0_54 ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_745]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_15,plain,
% 15.49/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.49/2.51      | r1_lattices(X0,X3,X1)
% 15.49/2.51      | ~ r2_hidden(X3,X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f64]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_29,negated_conjecture,
% 15.49/2.51      ( ~ v2_struct_0(sK4) ),
% 15.49/2.51      inference(cnf_transformation,[],[f83]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_970,plain,
% 15.49/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.49/2.51      | r1_lattices(X0,X3,X1)
% 15.49/2.51      | ~ r2_hidden(X3,X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_971,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | r1_lattices(sK4,X2,X0)
% 15.49/2.51      | ~ r2_hidden(X2,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_970]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_975,plain,
% 15.49/2.51      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ r2_hidden(X2,X1)
% 15.49/2.51      | r1_lattices(sK4,X2,X0)
% 15.49/2.51      | ~ r4_lattice3(sK4,X0,X1) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_971,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_976,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | r1_lattices(sK4,X2,X0)
% 15.49/2.51      | ~ r2_hidden(X2,X1)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_975]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2100,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | r1_lattices(sK4,X1_54,X0_54)
% 15.49/2.51      | ~ r2_hidden(X1_54,X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_976]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_37144,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | r1_lattices(sK4,X1_54,sK2(sK4,X0_55,X0_54))
% 15.49/2.51      | ~ r2_hidden(X1_54,X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK2(sK4,X0_55,X0_54),u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X0_55) = X0_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_2109,c_2100]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_37156,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | r1_lattices(sK4,X1_54,sK2(sK4,X0_55,X0_54))
% 15.49/2.51      | ~ r2_hidden(X1_54,X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X0_55) = X0_54 ),
% 15.49/2.51      inference(backward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_2110,c_37144]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_16,plain,
% 15.49/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.49/2.51      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ v4_lattice3(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | k15_lattice3(X0,X2) = X1 ),
% 15.49/2.51      inference(cnf_transformation,[],[f72]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_763,plain,
% 15.49/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.49/2.51      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | k15_lattice3(X0,X2) = X1
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_764,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4)
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_763]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_768,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 15.49/2.51      | ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_764,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_769,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | ~ r1_lattices(sK4,X0,sK2(sK4,X1,X0))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X1) = X0 ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_768]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2108,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | ~ r1_lattices(sK4,X0_54,sK2(sK4,X0_55,X0_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X0_55) = X0_54 ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_769]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_37240,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | ~ r2_hidden(X0_54,X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | k15_lattice3(sK4,X0_55) = X0_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_37156,c_2108]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2124,plain,
% 15.49/2.51      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 15.49/2.51      theory(equality) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2122,plain,( X0_54 = X0_54 ),theory(equality) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3084,plain,
% 15.49/2.51      ( X0_54 != X1_54 | X1_54 = X0_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_2124,c_2122]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_37598,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | ~ r2_hidden(X0_54,X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | X0_54 = k15_lattice3(sK4,X0_55) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_37240,c_3084]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_25,negated_conjecture,
% 15.49/2.51      ( k4_filter_0(sK4,sK5,sK6) != k15_lattice3(sK4,a_3_6_lattice3(sK4,sK5,sK6)) ),
% 15.49/2.51      inference(cnf_transformation,[],[f87]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2120,negated_conjecture,
% 15.49/2.51      ( k4_filter_0(sK4,sK5,sK6) != k15_lattice3(sK4,a_3_6_lattice3(sK4,sK5,sK6)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_25]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_41306,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,k4_filter_0(sK4,sK5,sK6),a_3_6_lattice3(sK4,sK5,sK6))
% 15.49/2.51      | ~ r2_hidden(k4_filter_0(sK4,sK5,sK6),a_3_6_lattice3(sK4,sK5,sK6))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,sK5,sK6),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_37598,c_2120]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_31,negated_conjecture,
% 15.49/2.51      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(cnf_transformation,[],[f81]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_30,negated_conjecture,
% 15.49/2.51      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(cnf_transformation,[],[f82]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_21,plain,
% 15.49/2.51      ( ~ r3_lattices(X0,k4_lattices(X0,X1,X2),X3)
% 15.49/2.51      | r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.49/2.51      | ~ v4_lattice3(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f92]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_646,plain,
% 15.49/2.51      ( ~ r3_lattices(X0,k4_lattices(X0,X1,X2),X3)
% 15.49/2.51      | r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_647,plain,
% 15.49/2.51      ( ~ r3_lattices(sK4,k4_lattices(sK4,X0,X1),X2)
% 15.49/2.51      | r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_646]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_651,plain,
% 15.49/2.51      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
% 15.49/2.51      | ~ r3_lattices(sK4,k4_lattices(sK4,X0,X1),X2) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_647,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_652,plain,
% 15.49/2.51      ( ~ r3_lattices(sK4,k4_lattices(sK4,X0,X1),X2)
% 15.49/2.51      | r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_651]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2113,plain,
% 15.49/2.51      ( ~ r3_lattices(sK4,k4_lattices(sK4,X0_54,X1_54),X2_54)
% 15.49/2.51      | r2_hidden(X1_54,a_3_6_lattice3(sK4,X0_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_652]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2747,plain,
% 15.49/2.51      ( ~ r3_lattices(sK4,k4_lattices(sK4,X0_54,k4_filter_0(sK4,X0_54,X1_54)),X1_54)
% 15.49/2.51      | r2_hidden(k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,X0_54,X1_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(instantiation,[status(thm)],[c_2113]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5454,plain,
% 15.49/2.51      ( ~ r3_lattices(sK4,k4_lattices(sK4,sK5,k4_filter_0(sK4,sK5,sK6)),sK6)
% 15.49/2.51      | r2_hidden(k4_filter_0(sK4,sK5,sK6),a_3_6_lattice3(sK4,sK5,sK6))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,sK5,sK6),u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(instantiation,[status(thm)],[c_2747]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_11,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.49/2.51      | m1_subset_1(k4_filter_0(X1,X2,X0),u1_struct_0(X1))
% 15.49/2.51      | ~ l3_lattices(X1)
% 15.49/2.51      | v2_struct_0(X1)
% 15.49/2.51      | ~ v10_lattices(X1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f63]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_28,negated_conjecture,
% 15.49/2.51      ( v10_lattices(sK4) ),
% 15.49/2.51      inference(cnf_transformation,[],[f84]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_927,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.49/2.51      | m1_subset_1(k4_filter_0(X1,X2,X0),u1_struct_0(X1))
% 15.49/2.51      | ~ l3_lattices(X1)
% 15.49/2.51      | v2_struct_0(X1)
% 15.49/2.51      | sK4 != X1 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_928,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_927]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_932,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_928,c_35,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_933,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(k4_filter_0(sK4,X1,X0),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_932]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2103,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(k4_filter_0(sK4,X1_54,X0_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_933]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_8894,plain,
% 15.49/2.51      ( m1_subset_1(k4_filter_0(sK4,sK5,sK6),u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(instantiation,[status(thm)],[c_2103]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_10,plain,
% 15.49/2.51      ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
% 15.49/2.51      | ~ v3_filter_0(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f89]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_27,negated_conjecture,
% 15.49/2.51      ( v3_filter_0(sK4) ),
% 15.49/2.51      inference(cnf_transformation,[],[f85]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_445,plain,
% 15.49/2.51      ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_446,plain,
% 15.49/2.51      ( r3_lattices(sK4,k4_lattices(sK4,X0,k4_filter_0(sK4,X0,X1)),X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_445]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_450,plain,
% 15.49/2.51      ( ~ m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | r3_lattices(sK4,k4_lattices(sK4,X0,k4_filter_0(sK4,X0,X1)),X1) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_446,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_451,plain,
% 15.49/2.51      ( r3_lattices(sK4,k4_lattices(sK4,X0,k4_filter_0(sK4,X0,X1)),X1)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_450]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_961,plain,
% 15.49/2.51      ( r3_lattices(sK4,k4_lattices(sK4,X0,k4_filter_0(sK4,X0,X1)),X1)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(backward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_933,c_451]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2102,plain,
% 15.49/2.51      ( r3_lattices(sK4,k4_lattices(sK4,X0_54,k4_filter_0(sK4,X0_54,X1_54)),X1_54)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_961]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_15538,plain,
% 15.49/2.51      ( r3_lattices(sK4,k4_lattices(sK4,sK5,k4_filter_0(sK4,sK5,sK6)),sK6)
% 15.49/2.51      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(instantiation,[status(thm)],[c_2102]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_41449,plain,
% 15.49/2.51      ( ~ r4_lattice3(sK4,k4_filter_0(sK4,sK5,sK6),a_3_6_lattice3(sK4,sK5,sK6)) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_41306,c_31,c_30,c_5454,c_8894,c_15538]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_23,plain,
% 15.49/2.51      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.49/2.51      | ~ v4_lattice3(X1)
% 15.49/2.51      | ~ l3_lattices(X1)
% 15.49/2.51      | v2_struct_0(X1)
% 15.49/2.51      | ~ v10_lattices(X1)
% 15.49/2.51      | sK3(X0,X1,X2,X3) = X0 ),
% 15.49/2.51      inference(cnf_transformation,[],[f74]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_811,plain,
% 15.49/2.51      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.49/2.51      | ~ l3_lattices(X1)
% 15.49/2.51      | v2_struct_0(X1)
% 15.49/2.51      | ~ v10_lattices(X1)
% 15.49/2.51      | sK3(X0,X1,X2,X3) = X0
% 15.49/2.51      | sK4 != X1 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_812,plain,
% 15.49/2.51      ( ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4)
% 15.49/2.51      | sK3(X0,sK4,X1,X2) = X0 ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_811]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_816,plain,
% 15.49/2.51      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
% 15.49/2.51      | sK3(X0,sK4,X1,X2) = X0 ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_812,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_817,plain,
% 15.49/2.51      ( ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | sK3(X0,sK4,X1,X2) = X0 ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_816]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2106,plain,
% 15.49/2.51      ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | sK3(X0_54,sK4,X1_54,X2_54) = X0_54 ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_817]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4962,plain,
% 15.49/2.51      ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | X0_54 = sK3(X0_54,sK4,X1_54,X2_54) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_3084,c_2106]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2125,plain,
% 15.49/2.51      ( ~ r3_lattices(X0_53,X0_54,X1_54)
% 15.49/2.51      | r3_lattices(X0_53,X2_54,X3_54)
% 15.49/2.51      | X2_54 != X0_54
% 15.49/2.51      | X3_54 != X1_54 ),
% 15.49/2.51      theory(equality) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5099,plain,
% 15.49/2.51      ( r3_lattices(X0_53,X0_54,X1_54)
% 15.49/2.51      | ~ r3_lattices(X0_53,X2_54,sK3(X1_54,sK4,X3_54,X4_54))
% 15.49/2.51      | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X3_54,X4_54))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X4_54,u1_struct_0(sK4))
% 15.49/2.51      | X0_54 != X2_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_4962,c_2125]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2126,plain,
% 15.49/2.51      ( ~ r1_lattices(X0_53,X0_54,X1_54)
% 15.49/2.51      | r1_lattices(X0_53,X2_54,X3_54)
% 15.49/2.51      | X2_54 != X0_54
% 15.49/2.51      | X3_54 != X1_54 ),
% 15.49/2.51      theory(equality) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3951,plain,
% 15.49/2.51      ( ~ r1_lattices(X0_53,X0_54,X1_54)
% 15.49/2.51      | r1_lattices(X0_53,X2_54,sK3(X1_54,sK4,X3_54,X4_54))
% 15.49/2.51      | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X3_54,X4_54))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X4_54,u1_struct_0(sK4))
% 15.49/2.51      | X2_54 != X0_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_2126,c_2106]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4298,plain,
% 15.49/2.51      ( ~ r1_lattices(X0_53,X0_54,X1_54)
% 15.49/2.51      | r1_lattices(X0_53,X0_54,sK3(X1_54,sK4,X2_54,X3_54))
% 15.49/2.51      | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X2_54,X3_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_3951,c_2122]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_0,plain,
% 15.49/2.51      ( ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | v9_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f55]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4,plain,
% 15.49/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.49/2.51      | r3_lattices(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ v6_lattices(X0)
% 15.49/2.51      | ~ v8_lattices(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v9_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f57]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_397,plain,
% 15.49/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.49/2.51      | r3_lattices(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ v6_lattices(X0)
% 15.49/2.51      | ~ v8_lattices(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2,plain,
% 15.49/2.51      ( v6_lattices(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f53]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1,plain,
% 15.49/2.51      ( v8_lattices(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f54]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_401,plain,
% 15.49/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.49/2.51      | r3_lattices(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_397,c_2,c_1]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_879,plain,
% 15.49/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.49/2.51      | r3_lattices(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_401,c_28]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_880,plain,
% 15.49/2.51      ( ~ r1_lattices(sK4,X0,X1)
% 15.49/2.51      | r3_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_879]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_884,plain,
% 15.49/2.51      ( ~ r1_lattices(sK4,X0,X1)
% 15.49/2.51      | r3_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_880,c_35,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_885,plain,
% 15.49/2.51      ( ~ r1_lattices(sK4,X0,X1)
% 15.49/2.51      | r3_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_884]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2105,plain,
% 15.49/2.51      ( ~ r1_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | r3_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_885]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_6700,plain,
% 15.49/2.51      ( ~ r1_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | r3_lattices(sK4,X0_54,sK3(X1_54,sK4,X2_54,X3_54))
% 15.49/2.51      | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X2_54,X3_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK3(X1_54,sK4,X2_54,X3_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_4298,c_2105]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_24,plain,
% 15.49/2.51      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.49/2.51      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
% 15.49/2.51      | ~ v4_lattice3(X1)
% 15.49/2.51      | ~ l3_lattices(X1)
% 15.49/2.51      | v2_struct_0(X1)
% 15.49/2.51      | ~ v10_lattices(X1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f73]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_787,plain,
% 15.49/2.51      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.49/2.51      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
% 15.49/2.51      | ~ l3_lattices(X1)
% 15.49/2.51      | v2_struct_0(X1)
% 15.49/2.51      | ~ v10_lattices(X1)
% 15.49/2.51      | sK4 != X1 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_788,plain,
% 15.49/2.51      ( ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK3(X0,sK4,X1,X2),u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_787]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_792,plain,
% 15.49/2.51      ( m1_subset_1(sK3(X0,sK4,X1,X2),u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2)) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_788,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_793,plain,
% 15.49/2.51      ( ~ r2_hidden(X0,a_3_6_lattice3(sK4,X1,X2))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK3(X0,sK4,X1,X2),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_792]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2107,plain,
% 15.49/2.51      ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK3(X0_54,sK4,X1_54,X2_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_793]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_6791,plain,
% 15.49/2.51      ( ~ r1_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | r3_lattices(sK4,X0_54,sK3(X1_54,sK4,X2_54,X3_54))
% 15.49/2.51      | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X2_54,X3_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(forward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_6700,c_2107]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_25083,plain,
% 15.49/2.51      ( ~ r1_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | r3_lattices(sK4,X2_54,X1_54)
% 15.49/2.51      | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X3_54,X4_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X4_54,u1_struct_0(sK4))
% 15.49/2.51      | X2_54 != X0_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_5099,c_6791]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3610,plain,
% 15.49/2.51      ( r2_hidden(k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,X0_54,X1_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_2102,c_2113]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3708,plain,
% 15.49/2.51      ( r2_hidden(k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(forward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_3610,c_2103]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_35358,plain,
% 15.49/2.51      ( ~ r1_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | r3_lattices(sK4,X3_54,k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | X3_54 != X0_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_25083,c_3708]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3955,plain,
% 15.49/2.51      ( ~ r1_lattices(X0_53,X0_54,X1_54)
% 15.49/2.51      | r1_lattices(X0_53,X2_54,X1_54)
% 15.49/2.51      | X2_54 != X0_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_2126,c_2122]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5782,plain,
% 15.49/2.51      ( r1_lattices(X0_53,X0_54,X1_54)
% 15.49/2.51      | ~ r1_lattices(X0_53,sK3(X0_54,sK4,X2_54,X3_54),X1_54)
% 15.49/2.51      | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X2_54,X3_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_3955,c_4962]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5,plain,
% 15.49/2.51      ( r1_lattices(X0,X1,X2)
% 15.49/2.51      | ~ r3_lattices(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ v6_lattices(X0)
% 15.49/2.51      | ~ v8_lattices(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v9_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f56]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_365,plain,
% 15.49/2.51      ( r1_lattices(X0,X1,X2)
% 15.49/2.51      | ~ r3_lattices(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ v6_lattices(X0)
% 15.49/2.51      | ~ v8_lattices(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_0,c_5]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_369,plain,
% 15.49/2.51      ( r1_lattices(X0,X1,X2)
% 15.49/2.51      | ~ r3_lattices(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_365,c_2,c_1]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_903,plain,
% 15.49/2.51      ( r1_lattices(X0,X1,X2)
% 15.49/2.51      | ~ r3_lattices(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_369,c_28]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_904,plain,
% 15.49/2.51      ( r1_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ r3_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_903]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_908,plain,
% 15.49/2.51      ( r1_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ r3_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_904,c_35,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_909,plain,
% 15.49/2.51      ( r1_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ r3_lattices(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_908]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2104,plain,
% 15.49/2.51      ( r1_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | ~ r3_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_909]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_11159,plain,
% 15.49/2.51      ( r1_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | ~ r3_lattices(sK4,sK3(X0_54,sK4,X2_54,X3_54),X1_54)
% 15.49/2.51      | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X2_54,X3_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK3(X0_54,sK4,X2_54,X3_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_5782,c_2104]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_11175,plain,
% 15.49/2.51      ( r1_lattices(sK4,X0_54,X1_54)
% 15.49/2.51      | ~ r3_lattices(sK4,sK3(X0_54,sK4,X2_54,X3_54),X1_54)
% 15.49/2.51      | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X2_54,X3_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(forward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_11159,c_2107]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_9,plain,
% 15.49/2.51      ( r3_lattices(X0,X1,k4_filter_0(X0,X2,X3))
% 15.49/2.51      | ~ r3_lattices(X0,k4_lattices(X0,X2,X1),X3)
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(X0,X2,X3),u1_struct_0(X0))
% 15.49/2.51      | ~ v3_filter_0(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f88]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_469,plain,
% 15.49/2.51      ( r3_lattices(X0,X1,k4_filter_0(X0,X2,X3))
% 15.49/2.51      | ~ r3_lattices(X0,k4_lattices(X0,X2,X1),X3)
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(X0,X2,X3),u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_470,plain,
% 15.49/2.51      ( r3_lattices(sK4,X0,k4_filter_0(sK4,X1,X2))
% 15.49/2.51      | ~ r3_lattices(sK4,k4_lattices(sK4,X1,X0),X2)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,X1,X2),u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_469]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_474,plain,
% 15.49/2.51      ( ~ m1_subset_1(k4_filter_0(sK4,X1,X2),u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ r3_lattices(sK4,k4_lattices(sK4,X1,X0),X2)
% 15.49/2.51      | r3_lattices(sK4,X0,k4_filter_0(sK4,X1,X2)) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_470,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_475,plain,
% 15.49/2.51      ( r3_lattices(sK4,X0,k4_filter_0(sK4,X1,X2))
% 15.49/2.51      | ~ r3_lattices(sK4,k4_lattices(sK4,X1,X0),X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,X1,X2),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_474]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_962,plain,
% 15.49/2.51      ( r3_lattices(sK4,X0,k4_filter_0(sK4,X1,X2))
% 15.49/2.51      | ~ r3_lattices(sK4,k4_lattices(sK4,X1,X0),X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(backward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_933,c_475]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2101,plain,
% 15.49/2.51      ( r3_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ r3_lattices(sK4,k4_lattices(sK4,X1_54,X0_54),X2_54)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_962]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_22,plain,
% 15.49/2.51      ( r3_lattices(X0,k4_lattices(X0,X1,sK3(X2,X0,X1,X3)),X3)
% 15.49/2.51      | ~ r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.49/2.51      | ~ v4_lattice3(X0)
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f75]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_622,plain,
% 15.49/2.51      ( r3_lattices(X0,k4_lattices(X0,X1,sK3(X2,X0,X1,X3)),X3)
% 15.49/2.51      | ~ r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0)
% 15.49/2.51      | ~ v10_lattices(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_623,plain,
% 15.49/2.51      ( r3_lattices(sK4,k4_lattices(sK4,X0,sK3(X1,sK4,X0,X2)),X2)
% 15.49/2.51      | ~ r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4)
% 15.49/2.51      | v2_struct_0(sK4)
% 15.49/2.51      | ~ v10_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_622]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_627,plain,
% 15.49/2.51      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
% 15.49/2.51      | r3_lattices(sK4,k4_lattices(sK4,X0,sK3(X1,sK4,X0,X2)),X2) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_623,c_35,c_34,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_628,plain,
% 15.49/2.51      ( r3_lattices(sK4,k4_lattices(sK4,X0,sK3(X1,sK4,X0,X2)),X2)
% 15.49/2.51      | ~ r2_hidden(X1,a_3_6_lattice3(sK4,X0,X2))
% 15.49/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_627]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2114,plain,
% 15.49/2.51      ( r3_lattices(sK4,k4_lattices(sK4,X0_54,sK3(X1_54,sK4,X0_54,X2_54)),X2_54)
% 15.49/2.51      | ~ r2_hidden(X1_54,a_3_6_lattice3(sK4,X0_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_628]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4092,plain,
% 15.49/2.51      ( r3_lattices(sK4,sK3(X0_54,sK4,X1_54,X2_54),k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK3(X0_54,sK4,X1_54,X2_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_2101,c_2114]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4489,plain,
% 15.49/2.51      ( ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | r3_lattices(sK4,sK3(X0_54,sK4,X1_54,X2_54),k4_filter_0(sK4,X1_54,X2_54)) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_4092,c_2107]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4490,plain,
% 15.49/2.51      ( r3_lattices(sK4,sK3(X0_54,sK4,X1_54,X2_54),k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_4489]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_11204,plain,
% 15.49/2.51      ( r1_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,X1_54,X2_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_11175,c_4490]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_15706,plain,
% 15.49/2.51      ( r1_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(forward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_11204,c_2103]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_35525,plain,
% 15.49/2.51      ( r3_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ r2_hidden(X3_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X3_54,u1_struct_0(sK4))
% 15.49/2.51      | X0_54 != X3_54 ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_35358,c_15706]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2127,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0_54,X0_56)
% 15.49/2.51      | m1_subset_1(X1_54,X0_56)
% 15.49/2.51      | X1_54 != X0_54 ),
% 15.49/2.51      theory(equality) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5107,plain,
% 15.49/2.51      ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | m1_subset_1(X0_54,X0_56)
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK3(X0_54,sK4,X1_54,X2_54),X0_56) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_4962,c_2127]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5523,plain,
% 15.49/2.51      ( ~ r2_hidden(X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_5107,c_2107]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_35541,plain,
% 15.49/2.51      ( r3_lattices(sK4,X0_54,k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ r2_hidden(X3_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | X0_54 != X3_54 ),
% 15.49/2.51      inference(forward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_35525,c_5523]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_13,plain,
% 15.49/2.51      ( r4_lattice3(X0,X1,X2)
% 15.49/2.51      | r2_hidden(sK1(X0,X1,X2),X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f66]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1018,plain,
% 15.49/2.51      ( r4_lattice3(X0,X1,X2)
% 15.49/2.51      | r2_hidden(sK1(X0,X1,X2),X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1019,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | r2_hidden(sK1(sK4,X0,X1),X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_1018]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1023,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | r2_hidden(sK1(sK4,X0,X1),X1)
% 15.49/2.51      | r4_lattice3(sK4,X0,X1) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_1019,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1024,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | r2_hidden(sK1(sK4,X0,X1),X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_1023]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2098,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | r2_hidden(sK1(sK4,X0_54,X0_55),X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_1024]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_35684,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | r3_lattices(sK4,X3_54,k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | X3_54 != sK1(sK4,X0_54,a_3_6_lattice3(sK4,X1_54,X2_54)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_35541,c_2098]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_35742,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0_54,a_3_6_lattice3(sK4,X1_54,X2_54))
% 15.49/2.51      | r3_lattices(sK4,sK1(sK4,X0_54,a_3_6_lattice3(sK4,X1_54,X2_54)),k4_filter_0(sK4,X1_54,X2_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X2_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_35684,c_2122]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_12,plain,
% 15.49/2.51      ( r4_lattice3(X0,X1,X2)
% 15.49/2.51      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f67]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1039,plain,
% 15.49/2.51      ( r4_lattice3(X0,X1,X2)
% 15.49/2.51      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1040,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_1039]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1044,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 15.49/2.51      | r4_lattice3(sK4,X0,X1) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_1040,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1045,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_1044]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2097,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | ~ r1_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_1045]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3337,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK1(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_2097,c_2104]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_14,plain,
% 15.49/2.51      ( r4_lattice3(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | v2_struct_0(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f65]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_997,plain,
% 15.49/2.51      ( r4_lattice3(X0,X1,X2)
% 15.49/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.49/2.51      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 15.49/2.51      | ~ l3_lattices(X0)
% 15.49/2.51      | sK4 != X0 ),
% 15.49/2.51      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_998,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 15.49/2.51      | ~ l3_lattices(sK4) ),
% 15.49/2.51      inference(unflattening,[status(thm)],[c_997]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1002,plain,
% 15.49/2.51      ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | r4_lattice3(sK4,X0,X1) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_998,c_32]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1003,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_1002]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2099,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | m1_subset_1(sK1(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(subtyping,[status(esa)],[c_1003]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3615,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
% 15.49/2.51      | r4_lattice3(sK4,X0_54,X0_55) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_3337,c_2099]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3616,plain,
% 15.49/2.51      ( r4_lattice3(sK4,X0_54,X0_55)
% 15.49/2.51      | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_3615]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_36834,plain,
% 15.49/2.51      ( r4_lattice3(sK4,k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(k4_filter_0(sK4,X0_54,X1_54),u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_35742,c_3616]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_36978,plain,
% 15.49/2.51      ( r4_lattice3(sK4,k4_filter_0(sK4,X0_54,X1_54),a_3_6_lattice3(sK4,X0_54,X1_54))
% 15.49/2.51      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(forward_subsumption_resolution,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_36834,c_2103]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_41461,plain,
% 15.49/2.51      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 15.49/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 15.49/2.51      inference(resolution,[status(thm)],[c_41449,c_36978]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(contradiction,plain,
% 15.49/2.51      ( $false ),
% 15.49/2.51      inference(minisat,[status(thm)],[c_41461,c_30,c_31]) ).
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.49/2.51  
% 15.49/2.51  ------                               Statistics
% 15.49/2.51  
% 15.49/2.51  ------ Selected
% 15.49/2.51  
% 15.49/2.51  total_time:                             1.705
% 15.49/2.51  
%------------------------------------------------------------------------------

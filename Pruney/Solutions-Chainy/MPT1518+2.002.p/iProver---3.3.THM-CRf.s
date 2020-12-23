%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:22 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :  223 (1499 expanded)
%              Number of clauses        :  149 ( 351 expanded)
%              Number of leaves         :   17 ( 473 expanded)
%              Depth                    :   27
%              Number of atoms          : 1277 (14250 expanded)
%              Number of equality atoms :  159 (1478 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(cnf_transformation,[],[f26])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
          & l3_lattices(X0)
          & v3_filter_0(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k4_filter_0(X0,X1,sK5) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,sK5))
        & l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
            ( k4_filter_0(X0,sK4,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,sK4,X2))
            & l3_lattices(X0)
            & v3_filter_0(X0)
            & v10_lattices(X0)
            & ~ v2_struct_0(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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
              ( k4_filter_0(sK3,X1,X2) != k15_lattice3(sK3,a_3_6_lattice3(sK3,X1,X2))
              & l3_lattices(sK3)
              & v3_filter_0(sK3)
              & v10_lattices(sK3)
              & ~ v2_struct_0(sK3)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v4_lattice3(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k4_filter_0(sK3,sK4,sK5) != k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5))
    & l3_lattices(sK3)
    & v3_filter_0(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v4_lattice3(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f45,f44,f43])).

fof(f70,plain,(
    v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    k4_filter_0(sK3,sK4,sK5) != k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f53,plain,(
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

fof(f80,plain,(
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
    inference(equality_resolution,[],[f53])).

fof(f76,plain,(
    v3_filter_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r3_lattices(X1,k4_lattices(X1,X2,X5),X3)
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r3_lattices(X1,k4_lattices(X1,X2,sK2(X0,X1,X2,X3)),X3)
        & sK2(X0,X1,X2,X3) = X0
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,k4_lattices(X1,X2,sK2(X0,X1,X2,X3)),X3)
            & sK2(X0,X1,X2,X3) = X0
            & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(X0,X1,X2,X3) = X0
      | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f54,plain,(
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

fof(f79,plain,(
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
    inference(equality_resolution,[],[f54])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X1,k4_lattices(X1,X2,sK2(X0,X1,X2,X3)),X3)
      | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f50,plain,(
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

fof(f51,plain,(
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

fof(f48,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_20,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,negated_conjecture,
    ( v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_448,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_449,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3)
    | k15_lattice3(sK3,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,X1)
    | ~ r4_lattice3(sK3,X0,X1)
    | k15_lattice3(sK3,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_31,c_30,c_28])).

cnf(c_454,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k15_lattice3(sK3,X1) = X0 ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_1839,plain,
    ( ~ r4_lattice3(sK3,X0_53,X0_54)
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | k15_lattice3(sK3,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_1848,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_1846,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2865,plain,
    ( X0_53 != X1_53
    | X1_53 = X0_53 ),
    inference(resolution,[status(thm)],[c_1848,c_1846])).

cnf(c_30195,plain,
    ( ~ r4_lattice3(sK3,X0_53,X0_54)
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | X0_53 = k15_lattice3(sK3,X0_54) ),
    inference(resolution,[status(thm)],[c_1839,c_2865])).

cnf(c_21,negated_conjecture,
    ( k4_filter_0(sK3,sK4,sK5) != k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1844,negated_conjecture,
    ( k4_filter_0(sK3,sK4,sK5) != k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_30481,plain,
    ( ~ r4_lattice3(sK3,k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
    | ~ r2_hidden(k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(k4_filter_0(sK3,sK4,sK5),u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_30195,c_1844])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1843,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2208,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1843])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_filter_0(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_filter_0(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_779,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_775,c_31,c_28])).

cnf(c_780,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k4_filter_0(sK3,X1,X0),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_779])).

cnf(c_10,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
    | ~ v3_filter_0(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_23,negated_conjecture,
    ( v3_filter_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_549,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_550,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0,k4_filter_0(sK3,X0,X1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_554,plain,
    ( ~ m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r3_lattices(sK3,k4_lattices(sK3,X0,k4_filter_0(sK3,X0,X1)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_31,c_30,c_28])).

cnf(c_555,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0,k4_filter_0(sK3,X0,X1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_554])).

cnf(c_808,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0,k4_filter_0(sK3,X0,X1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_780,c_555])).

cnf(c_1832,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0_53,k4_filter_0(sK3,X0_53,X1_53)),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_808])).

cnf(c_2219,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0_53,k4_filter_0(sK3,X0_53,X1_53)),X1_53) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1832])).

cnf(c_16,plain,
    ( ~ r3_lattices(X0,k4_lattices(X0,X1,X2),X3)
    | r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_496,plain,
    ( ~ r3_lattices(X0,k4_lattices(X0,X1,X2),X3)
    | r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_497,plain,
    ( ~ r3_lattices(sK3,k4_lattices(sK3,X0,X1),X2)
    | r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
    | ~ r3_lattices(sK3,k4_lattices(sK3,X0,X1),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_31,c_30,c_28])).

cnf(c_502,plain,
    ( ~ r3_lattices(sK3,k4_lattices(sK3,X0,X1),X2)
    | r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_501])).

cnf(c_1837,plain,
    ( ~ r3_lattices(sK3,k4_lattices(sK3,X0_53,X1_53),X2_53)
    | r2_hidden(X1_53,a_3_6_lattice3(sK3,X0_53,X2_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_502])).

cnf(c_2214,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0_53,X1_53),X2_53) != iProver_top
    | r2_hidden(X1_53,a_3_6_lattice3(sK3,X0_53,X2_53)) = iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1837])).

cnf(c_3076,plain,
    ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_2214])).

cnf(c_3008,plain,
    ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_1832,c_1837])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | m1_subset_1(k4_filter_0(sK3,X1_53,X0_53),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_780])).

cnf(c_2218,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_2378,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2218])).

cnf(c_2451,plain,
    ( ~ r3_lattices(sK3,k4_lattices(sK3,X0_53,k4_filter_0(sK3,X0_53,X1_53)),X1_53)
    | r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_3079,plain,
    ( ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3008,c_1832,c_2378,c_2451])).

cnf(c_3080,plain,
    ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_3079])).

cnf(c_3081,plain,
    ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3080])).

cnf(c_4151,plain,
    ( m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3076,c_3081])).

cnf(c_4152,plain,
    ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4151])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2,X3) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_424,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2,X3) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_425,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3)
    | sK2(X0,sK3,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
    | sK2(X0,sK3,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_31,c_30,c_28])).

cnf(c_430,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | sK2(X0,sK3,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_429])).

cnf(c_1840,plain,
    ( ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | sK2(X0_53,sK3,X1_53,X2_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_430])).

cnf(c_2211,plain,
    ( sK2(X0_53,sK3,X1_53,X2_53) = X0_53
    | r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1840])).

cnf(c_4158,plain,
    ( sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53) = k4_filter_0(sK3,X0_53,X1_53)
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4152,c_2211])).

cnf(c_4302,plain,
    ( sK2(k4_filter_0(sK3,X0_53,sK5),sK3,X0_53,sK5) = k4_filter_0(sK3,X0_53,sK5)
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2208,c_4158])).

cnf(c_4357,plain,
    ( sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5) = k4_filter_0(sK3,sK4,sK5)
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4302])).

cnf(c_2823,plain,
    ( k4_filter_0(sK3,X0_53,X1_53) = k4_filter_0(sK3,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_4886,plain,
    ( k4_filter_0(sK3,sK4,sK5) = k4_filter_0(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2823])).

cnf(c_2593,plain,
    ( ~ r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3))
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,X1_53)) = k4_filter_0(sK3,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_5039,plain,
    ( ~ r4_lattice3(sK3,k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
    | ~ r2_hidden(k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(k4_filter_0(sK3,sK4,sK5),u1_struct_0(sK3))
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) = k4_filter_0(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_6303,plain,
    ( ~ r3_lattices(sK3,k4_lattices(sK3,sK4,k4_filter_0(sK3,sK4,sK5)),sK5)
    | r2_hidden(k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(k4_filter_0(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2451])).

cnf(c_8433,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,sK4,k4_filter_0(sK3,sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_15849,plain,
    ( m1_subset_1(k4_filter_0(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_2774,plain,
    ( X0_53 != X1_53
    | k15_lattice3(sK3,X0_54) != X1_53
    | k15_lattice3(sK3,X0_54) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_3686,plain,
    ( X0_53 != k4_filter_0(sK3,X1_53,X2_53)
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,X1_53,X3_53)) = X0_53
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,X1_53,X3_53)) != k4_filter_0(sK3,X1_53,X2_53) ),
    inference(instantiation,[status(thm)],[c_2774])).

cnf(c_4917,plain,
    ( sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53) != k4_filter_0(sK3,X0_53,X1_53)
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,X2_53)) = sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53)
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,X2_53)) != k4_filter_0(sK3,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_3686])).

cnf(c_19954,plain,
    ( sK2(k4_filter_0(sK3,X0_53,sK5),sK3,X0_53,sK5) != k4_filter_0(sK3,X0_53,sK5)
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,sK5)) = sK2(k4_filter_0(sK3,X0_53,sK5),sK3,X0_53,sK5)
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,sK5)) != k4_filter_0(sK3,X0_53,sK5) ),
    inference(instantiation,[status(thm)],[c_4917])).

cnf(c_19955,plain,
    ( sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5) != k4_filter_0(sK3,sK4,sK5)
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) = sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5)
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) != k4_filter_0(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_19954])).

cnf(c_3784,plain,
    ( X0_53 != X1_53
    | k4_filter_0(sK3,X2_53,X3_53) != X1_53
    | k4_filter_0(sK3,X2_53,X3_53) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_6644,plain,
    ( X0_53 != k4_filter_0(sK3,X1_53,X2_53)
    | k4_filter_0(sK3,X1_53,X2_53) = X0_53
    | k4_filter_0(sK3,X1_53,X2_53) != k4_filter_0(sK3,X1_53,X2_53) ),
    inference(instantiation,[status(thm)],[c_3784])).

cnf(c_9134,plain,
    ( sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53) != k4_filter_0(sK3,X0_53,X1_53)
    | k4_filter_0(sK3,X0_53,X1_53) = sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53)
    | k4_filter_0(sK3,X0_53,X1_53) != k4_filter_0(sK3,X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_6644])).

cnf(c_20767,plain,
    ( sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5) != k4_filter_0(sK3,sK4,sK5)
    | k4_filter_0(sK3,sK4,sK5) = sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5)
    | k4_filter_0(sK3,sK4,sK5) != k4_filter_0(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_9134])).

cnf(c_2505,plain,
    ( k4_filter_0(sK3,sK4,sK5) != X0_53
    | k4_filter_0(sK3,sK4,sK5) = k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5))
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) != X0_53 ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_4603,plain,
    ( k4_filter_0(sK3,sK4,sK5) != sK2(k4_filter_0(sK3,sK4,X0_53),sK3,sK4,sK5)
    | k4_filter_0(sK3,sK4,sK5) = k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5))
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) != sK2(k4_filter_0(sK3,sK4,X0_53),sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2505])).

cnf(c_20768,plain,
    ( k4_filter_0(sK3,sK4,sK5) != sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5)
    | k4_filter_0(sK3,sK4,sK5) = k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5))
    | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) != sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_4603])).

cnf(c_30601,plain,
    ( ~ r4_lattice3(sK3,k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30481,c_27,c_36,c_26,c_1844,c_4357,c_4886,c_5039,c_6303,c_8433,c_15849,c_19955,c_20767,c_20768])).

cnf(c_5204,plain,
    ( ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | X0_53 = sK2(X0_53,sK3,X1_53,X2_53) ),
    inference(resolution,[status(thm)],[c_2865,c_1840])).

cnf(c_1849,plain,
    ( ~ r3_lattices(X0_52,X0_53,X1_53)
    | r3_lattices(X0_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_4037,plain,
    ( ~ r3_lattices(X0_52,X0_53,X1_53)
    | r3_lattices(X0_52,X2_53,X1_53)
    | X2_53 != X0_53 ),
    inference(resolution,[status(thm)],[c_1849,c_1846])).

cnf(c_5505,plain,
    ( r3_lattices(X0_52,X0_53,X1_53)
    | ~ r3_lattices(X0_52,sK2(X0_53,sK3,X2_53,X3_53),X1_53)
    | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X2_53,X3_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X3_53,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_5204,c_4037])).

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
    inference(cnf_transformation,[],[f79])).

cnf(c_573,plain,
    ( r3_lattices(X0,X1,k4_filter_0(X0,X2,X3))
    | ~ r3_lattices(X0,k4_lattices(X0,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k4_filter_0(X0,X2,X3),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_574,plain,
    ( r3_lattices(sK3,X0,k4_filter_0(sK3,X1,X2))
    | ~ r3_lattices(sK3,k4_lattices(sK3,X1,X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_filter_0(sK3,X1,X2),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_578,plain,
    ( ~ m1_subset_1(k4_filter_0(sK3,X1,X2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r3_lattices(sK3,k4_lattices(sK3,X1,X0),X2)
    | r3_lattices(sK3,X0,k4_filter_0(sK3,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_31,c_30,c_28])).

cnf(c_579,plain,
    ( r3_lattices(sK3,X0,k4_filter_0(sK3,X1,X2))
    | ~ r3_lattices(sK3,k4_lattices(sK3,X1,X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_filter_0(sK3,X1,X2),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_578])).

cnf(c_809,plain,
    ( r3_lattices(sK3,X0,k4_filter_0(sK3,X1,X2))
    | ~ r3_lattices(sK3,k4_lattices(sK3,X1,X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_780,c_579])).

cnf(c_1831,plain,
    ( r3_lattices(sK3,X0_53,k4_filter_0(sK3,X1_53,X2_53))
    | ~ r3_lattices(sK3,k4_lattices(sK3,X1_53,X0_53),X2_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_809])).

cnf(c_17,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,sK2(X2,X0,X1,X3)),X3)
    | ~ r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_472,plain,
    ( r3_lattices(X0,k4_lattices(X0,X1,sK2(X2,X0,X1,X3)),X3)
    | ~ r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_473,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0,sK2(X1,sK3,X0,X2)),X2)
    | ~ r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
    | r3_lattices(sK3,k4_lattices(sK3,X0,sK2(X1,sK3,X0,X2)),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_31,c_30,c_28])).

cnf(c_478,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0,sK2(X1,sK3,X0,X2)),X2)
    | ~ r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_477])).

cnf(c_1838,plain,
    ( r3_lattices(sK3,k4_lattices(sK3,X0_53,sK2(X1_53,sK3,X0_53,X2_53)),X2_53)
    | ~ r2_hidden(X1_53,a_3_6_lattice3(sK3,X0_53,X2_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_478])).

cnf(c_3341,plain,
    ( r3_lattices(sK3,sK2(X0_53,sK3,X1_53,X2_53),k4_filter_0(sK3,X1_53,X2_53))
    | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2(X0_53,sK3,X1_53,X2_53),u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_1831,c_1838])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_400,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_401,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(X0,sK3,X1,X2),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_405,plain,
    ( m1_subset_1(sK2(X0,sK3,X1,X2),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_31,c_30,c_28])).

cnf(c_406,plain,
    ( ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(X0,sK3,X1,X2),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_405])).

cnf(c_1841,plain,
    ( ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | m1_subset_1(sK2(X0_53,sK3,X1_53,X2_53),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_3574,plain,
    ( ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
    | r3_lattices(sK3,sK2(X0_53,sK3,X1_53,X2_53),k4_filter_0(sK3,X1_53,X2_53)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3341,c_1841])).

cnf(c_3575,plain,
    ( r3_lattices(sK3,sK2(X0_53,sK3,X1_53,X2_53),k4_filter_0(sK3,X1_53,X2_53))
    | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_3574])).

cnf(c_6193,plain,
    ( r3_lattices(sK3,X0_53,k4_filter_0(sK3,X1_53,X2_53))
    | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_5505,c_3575])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(cnf_transformation,[],[f51])).

cnf(c_320,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_324,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_2,c_1])).

cnf(c_750,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_24])).

cnf(c_751,plain,
    ( r1_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_755,plain,
    ( r1_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_31,c_28])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_886,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_887,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_891,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_887,c_28])).

cnf(c_892,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_891])).

cnf(c_947,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r3_lattices(sK3,X2,X3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | X0 != X3
    | sK1(sK3,X0,X1) != X2
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_755,c_892])).

cnf(c_948,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r3_lattices(sK3,sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_14,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_844,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_845,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_952,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r3_lattices(sK3,sK1(sK3,X0,X1),X0)
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_28,c_845])).

cnf(c_953,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r3_lattices(sK3,sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_952])).

cnf(c_1827,plain,
    ( r4_lattice3(sK3,X0_53,X0_54)
    | ~ r3_lattices(sK3,sK1(sK3,X0_53,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_953])).

cnf(c_6211,plain,
    ( r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54)
    | ~ r2_hidden(sK1(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_6193,c_1827])).

cnf(c_30023,plain,
    ( ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ r2_hidden(sK1(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54),a_3_6_lattice3(sK3,X0_53,X1_53))
    | r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6211,c_2378])).

cnf(c_30024,plain,
    ( r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54)
    | ~ r2_hidden(sK1(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_30023])).

cnf(c_13,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_865,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_866,plain,
    ( r4_lattice3(sK3,X0,X1)
    | r2_hidden(sK1(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_870,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X1)
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_866,c_28])).

cnf(c_871,plain,
    ( r4_lattice3(sK3,X0,X1)
    | r2_hidden(sK1(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_870])).

cnf(c_1829,plain,
    ( r4_lattice3(sK3,X0_53,X0_54)
    | r2_hidden(sK1(sK3,X0_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_871])).

cnf(c_30049,plain,
    ( r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_30024,c_1829])).

cnf(c_30164,plain,
    ( ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30049,c_2378])).

cnf(c_30165,plain,
    ( r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_30164])).

cnf(c_30613,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_30601,c_30165])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30613,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.38/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/2.00  
% 11.38/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.38/2.00  
% 11.38/2.00  ------  iProver source info
% 11.38/2.00  
% 11.38/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.38/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.38/2.00  git: non_committed_changes: false
% 11.38/2.00  git: last_make_outside_of_git: false
% 11.38/2.00  
% 11.38/2.00  ------ 
% 11.38/2.00  ------ Parsing...
% 11.38/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.38/2.00  ------ Proving...
% 11.38/2.00  ------ Problem Properties 
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  clauses                                 19
% 11.38/2.00  conjectures                             3
% 11.38/2.00  EPR                                     0
% 11.38/2.00  Horn                                    15
% 11.38/2.00  unary                                   3
% 11.38/2.00  binary                                  0
% 11.38/2.00  lits                                    71
% 11.38/2.00  lits eq                                 6
% 11.38/2.00  fd_pure                                 0
% 11.38/2.00  fd_pseudo                               0
% 11.38/2.00  fd_cond                                 0
% 11.38/2.00  fd_pseudo_cond                          4
% 11.38/2.00  AC symbols                              0
% 11.38/2.00  
% 11.38/2.00  ------ Input Options Time Limit: Unbounded
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  ------ 
% 11.38/2.00  Current options:
% 11.38/2.00  ------ 
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  ------ Proving...
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  % SZS status Theorem for theBenchmark.p
% 11.38/2.00  
% 11.38/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.38/2.00  
% 11.38/2.00  fof(f7,axiom,(
% 11.38/2.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 11.38/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f25,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f7])).
% 11.38/2.00  
% 11.38/2.00  fof(f26,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f25])).
% 11.38/2.00  
% 11.38/2.00  fof(f67,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f26])).
% 11.38/2.00  
% 11.38/2.00  fof(f8,conjecture,(
% 11.38/2.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))))))),
% 11.38/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f9,negated_conjecture,(
% 11.38/2.00    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))))))),
% 11.38/2.00    inference(negated_conjecture,[],[f8])).
% 11.38/2.00  
% 11.38/2.00  fof(f27,plain,(
% 11.38/2.00    ? [X0] : (? [X1] : (? [X2] : ((k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & (l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f9])).
% 11.38/2.00  
% 11.38/2.00  fof(f28,plain,(
% 11.38/2.00    ? [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f27])).
% 11.38/2.00  
% 11.38/2.00  fof(f45,plain,(
% 11.38/2.00    ( ! [X0,X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) => (k4_filter_0(X0,X1,sK5) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,sK5)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f44,plain,(
% 11.38/2.00    ( ! [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k4_filter_0(X0,sK4,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,sK4,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f43,plain,(
% 11.38/2.00    ? [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k4_filter_0(sK3,X1,X2) != k15_lattice3(sK3,a_3_6_lattice3(sK3,X1,X2)) & l3_lattices(sK3) & v3_filter_0(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f46,plain,(
% 11.38/2.00    ((k4_filter_0(sK3,sK4,sK5) != k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) & l3_lattices(sK3) & v3_filter_0(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 11.38/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f45,f44,f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f70,plain,(
% 11.38/2.00    v4_lattice3(sK3)),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f68,plain,(
% 11.38/2.00    ~v2_struct_0(sK3)),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f69,plain,(
% 11.38/2.00    v10_lattices(sK3)),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f71,plain,(
% 11.38/2.00    l3_lattices(sK3)),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f78,plain,(
% 11.38/2.00    k4_filter_0(sK3,sK4,sK5) != k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5))),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f72,plain,(
% 11.38/2.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f73,plain,(
% 11.38/2.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f4,axiom,(
% 11.38/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)))),
% 11.38/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f19,plain,(
% 11.38/2.00    ! [X0,X1,X2] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f4])).
% 11.38/2.00  
% 11.38/2.00  fof(f20,plain,(
% 11.38/2.00    ! [X0,X1,X2] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f19])).
% 11.38/2.00  
% 11.38/2.00  fof(f58,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f20])).
% 11.38/2.00  
% 11.38/2.00  fof(f75,plain,(
% 11.38/2.00    v10_lattices(sK3)),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f3,axiom,(
% 11.38/2.00    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_lattices(X0,k4_lattices(X0,X1,X4),X2) => r3_lattices(X0,X4,X3))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))))))))),
% 11.38/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f17,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : ((r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f3])).
% 11.38/2.00  
% 11.38/2.00  fof(f18,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f17])).
% 11.38/2.00  
% 11.38/2.00  fof(f30,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_filter_0(X0,X1,X2) = X3 | (? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) & ((! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | k4_filter_0(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(nnf_transformation,[],[f18])).
% 11.38/2.00  
% 11.38/2.00  fof(f31,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_filter_0(X0,X1,X2) = X3 | ? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) & ((! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | k4_filter_0(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f30])).
% 11.38/2.00  
% 11.38/2.00  fof(f32,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_filter_0(X0,X1,X2) = X3 | ? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) & ((! [X5] : (r3_lattices(X0,X5,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | k4_filter_0(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(rectify,[],[f31])).
% 11.38/2.00  
% 11.38/2.00  fof(f33,plain,(
% 11.38/2.00    ! [X3,X2,X1,X0] : (? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0))) => (~r3_lattices(X0,sK0(X0,X1,X2,X3),X3) & r3_lattices(X0,k4_lattices(X0,X1,sK0(X0,X1,X2,X3)),X2) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f34,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_filter_0(X0,X1,X2) = X3 | (~r3_lattices(X0,sK0(X0,X1,X2,X3),X3) & r3_lattices(X0,k4_lattices(X0,X1,sK0(X0,X1,X2,X3)),X2) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) & ((! [X5] : (r3_lattices(X0,X5,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | k4_filter_0(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 11.38/2.00  
% 11.38/2.00  fof(f53,plain,(
% 11.38/2.00    ( ! [X2,X0,X3,X1] : (r3_lattices(X0,k4_lattices(X0,X1,X3),X2) | k4_filter_0(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f34])).
% 11.38/2.00  
% 11.38/2.00  fof(f80,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2) | ~m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(equality_resolution,[],[f53])).
% 11.38/2.00  
% 11.38/2.00  fof(f76,plain,(
% 11.38/2.00    v3_filter_0(sK3)),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f6,axiom,(
% 11.38/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))),
% 11.38/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f23,plain,(
% 11.38/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))) | (~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 11.38/2.00    inference(ennf_transformation,[],[f6])).
% 11.38/2.00  
% 11.38/2.00  fof(f24,plain,(
% 11.38/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.38/2.00    inference(flattening,[],[f23])).
% 11.38/2.00  
% 11.38/2.00  fof(f39,plain,(
% 11.38/2.00    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ! [X4] : (~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.38/2.00    inference(nnf_transformation,[],[f24])).
% 11.38/2.00  
% 11.38/2.00  fof(f40,plain,(
% 11.38/2.00    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ! [X4] : (~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X5] : (r3_lattices(X1,k4_lattices(X1,X2,X5),X3) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.38/2.00    inference(rectify,[],[f39])).
% 11.38/2.00  
% 11.38/2.00  fof(f41,plain,(
% 11.38/2.00    ! [X3,X2,X1,X0] : (? [X5] : (r3_lattices(X1,k4_lattices(X1,X2,X5),X3) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (r3_lattices(X1,k4_lattices(X1,X2,sK2(X0,X1,X2,X3)),X3) & sK2(X0,X1,X2,X3) = X0 & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))))),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f42,plain,(
% 11.38/2.00    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ! [X4] : (~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)))) & ((r3_lattices(X1,k4_lattices(X1,X2,sK2(X0,X1,X2,X3)),X3) & sK2(X0,X1,X2,X3) = X0 & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.38/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 11.38/2.00  
% 11.38/2.00  fof(f66,plain,(
% 11.38/2.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f42])).
% 11.38/2.00  
% 11.38/2.00  fof(f81,plain,(
% 11.38/2.00    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,a_3_6_lattice3(X1,X2,X3)) | ~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.38/2.00    inference(equality_resolution,[],[f66])).
% 11.38/2.00  
% 11.38/2.00  fof(f64,plain,(
% 11.38/2.00    ( ! [X2,X0,X3,X1] : (sK2(X0,X1,X2,X3) = X0 | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f42])).
% 11.38/2.00  
% 11.38/2.00  fof(f54,plain,(
% 11.38/2.00    ( ! [X2,X0,X5,X3,X1] : (r3_lattices(X0,X5,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X0)) | k4_filter_0(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f34])).
% 11.38/2.00  
% 11.38/2.00  fof(f79,plain,(
% 11.38/2.00    ( ! [X2,X0,X5,X1] : (r3_lattices(X0,X5,k4_filter_0(X0,X1,X2)) | ~r3_lattices(X0,k4_lattices(X0,X1,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(equality_resolution,[],[f54])).
% 11.38/2.00  
% 11.38/2.00  fof(f65,plain,(
% 11.38/2.00    ( ! [X2,X0,X3,X1] : (r3_lattices(X1,k4_lattices(X1,X2,sK2(X0,X1,X2,X3)),X3) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f42])).
% 11.38/2.00  
% 11.38/2.00  fof(f63,plain,(
% 11.38/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f42])).
% 11.38/2.00  
% 11.38/2.00  fof(f1,axiom,(
% 11.38/2.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.38/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f10,plain,(
% 11.38/2.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.38/2.00    inference(pure_predicate_removal,[],[f1])).
% 11.38/2.00  
% 11.38/2.00  fof(f11,plain,(
% 11.38/2.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.38/2.00    inference(pure_predicate_removal,[],[f10])).
% 11.38/2.00  
% 11.38/2.00  fof(f12,plain,(
% 11.38/2.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 11.38/2.00    inference(pure_predicate_removal,[],[f11])).
% 11.38/2.00  
% 11.38/2.00  fof(f13,plain,(
% 11.38/2.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 11.38/2.00    inference(ennf_transformation,[],[f12])).
% 11.38/2.00  
% 11.38/2.00  fof(f14,plain,(
% 11.38/2.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 11.38/2.00    inference(flattening,[],[f13])).
% 11.38/2.00  
% 11.38/2.00  fof(f50,plain,(
% 11.38/2.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f14])).
% 11.38/2.00  
% 11.38/2.00  fof(f2,axiom,(
% 11.38/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 11.38/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f15,plain,(
% 11.38/2.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f2])).
% 11.38/2.00  
% 11.38/2.00  fof(f16,plain,(
% 11.38/2.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f15])).
% 11.38/2.00  
% 11.38/2.00  fof(f29,plain,(
% 11.38/2.00    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(nnf_transformation,[],[f16])).
% 11.38/2.00  
% 11.38/2.00  fof(f51,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f29])).
% 11.38/2.00  
% 11.38/2.00  fof(f48,plain,(
% 11.38/2.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f14])).
% 11.38/2.00  
% 11.38/2.00  fof(f49,plain,(
% 11.38/2.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f14])).
% 11.38/2.00  
% 11.38/2.00  fof(f5,axiom,(
% 11.38/2.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 11.38/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f21,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f5])).
% 11.38/2.00  
% 11.38/2.00  fof(f22,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f21])).
% 11.38/2.00  
% 11.38/2.00  fof(f35,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(nnf_transformation,[],[f22])).
% 11.38/2.00  
% 11.38/2.00  fof(f36,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(rectify,[],[f35])).
% 11.38/2.00  
% 11.38/2.00  fof(f37,plain,(
% 11.38/2.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f38,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 11.38/2.00  
% 11.38/2.00  fof(f62,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f38])).
% 11.38/2.00  
% 11.38/2.00  fof(f74,plain,(
% 11.38/2.00    ~v2_struct_0(sK3)),
% 11.38/2.00    inference(cnf_transformation,[],[f46])).
% 11.38/2.00  
% 11.38/2.00  fof(f60,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f38])).
% 11.38/2.00  
% 11.38/2.00  fof(f61,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f38])).
% 11.38/2.00  
% 11.38/2.00  cnf(c_20,plain,
% 11.38/2.00      ( ~ r4_lattice3(X0,X1,X2)
% 11.38/2.00      | ~ r2_hidden(X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ v4_lattice3(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0)
% 11.38/2.00      | k15_lattice3(X0,X2) = X1 ),
% 11.38/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_29,negated_conjecture,
% 11.38/2.00      ( v4_lattice3(sK3) ),
% 11.38/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_448,plain,
% 11.38/2.00      ( ~ r4_lattice3(X0,X1,X2)
% 11.38/2.00      | ~ r2_hidden(X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0)
% 11.38/2.00      | k15_lattice3(X0,X2) = X1
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_449,plain,
% 11.38/2.00      ( ~ r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | ~ r2_hidden(X0,X1)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3)
% 11.38/2.00      | ~ v10_lattices(sK3)
% 11.38/2.00      | k15_lattice3(sK3,X1) = X0 ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_448]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_31,negated_conjecture,
% 11.38/2.00      ( ~ v2_struct_0(sK3) ),
% 11.38/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30,negated_conjecture,
% 11.38/2.00      ( v10_lattices(sK3) ),
% 11.38/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_28,negated_conjecture,
% 11.38/2.00      ( l3_lattices(sK3) ),
% 11.38/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_453,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ r2_hidden(X0,X1)
% 11.38/2.00      | ~ r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | k15_lattice3(sK3,X1) = X0 ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_449,c_31,c_30,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_454,plain,
% 11.38/2.00      ( ~ r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | ~ r2_hidden(X0,X1)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | k15_lattice3(sK3,X1) = X0 ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_453]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1839,plain,
% 11.38/2.00      ( ~ r4_lattice3(sK3,X0_53,X0_54)
% 11.38/2.00      | ~ r2_hidden(X0_53,X0_54)
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | k15_lattice3(sK3,X0_54) = X0_53 ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_454]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1848,plain,
% 11.38/2.00      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 11.38/2.00      theory(equality) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1846,plain,( X0_53 = X0_53 ),theory(equality) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2865,plain,
% 11.38/2.00      ( X0_53 != X1_53 | X1_53 = X0_53 ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_1848,c_1846]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30195,plain,
% 11.38/2.00      ( ~ r4_lattice3(sK3,X0_53,X0_54)
% 11.38/2.00      | ~ r2_hidden(X0_53,X0_54)
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | X0_53 = k15_lattice3(sK3,X0_54) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_1839,c_2865]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_21,negated_conjecture,
% 11.38/2.00      ( k4_filter_0(sK3,sK4,sK5) != k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) ),
% 11.38/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1844,negated_conjecture,
% 11.38/2.00      ( k4_filter_0(sK3,sK4,sK5) != k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_21]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30481,plain,
% 11.38/2.00      ( ~ r4_lattice3(sK3,k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
% 11.38/2.00      | ~ r2_hidden(k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,sK4,sK5),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_30195,c_1844]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_27,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_36,plain,
% 11.38/2.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_26,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1843,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_26]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2208,plain,
% 11.38/2.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1843]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_11,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | m1_subset_1(k4_filter_0(X1,X2,X0),u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | ~ v10_lattices(X1) ),
% 11.38/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_24,negated_conjecture,
% 11.38/2.00      ( v10_lattices(sK3) ),
% 11.38/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_774,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | m1_subset_1(k4_filter_0(X1,X2,X0),u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | sK3 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_775,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_774]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_779,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_775,c_31,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_780,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(k4_filter_0(sK3,X1,X0),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_779]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_10,plain,
% 11.38/2.00      ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
% 11.38/2.00      | ~ v3_filter_0(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_23,negated_conjecture,
% 11.38/2.00      ( v3_filter_0(sK3) ),
% 11.38/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_549,plain,
% 11.38/2.00      ( r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0)
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_550,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0,k4_filter_0(sK3,X0,X1)),X1)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3)
% 11.38/2.00      | ~ v10_lattices(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_549]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_554,plain,
% 11.38/2.00      ( ~ m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | r3_lattices(sK3,k4_lattices(sK3,X0,k4_filter_0(sK3,X0,X1)),X1) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_550,c_31,c_30,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_555,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0,k4_filter_0(sK3,X0,X1)),X1)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X0,X1),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_554]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_808,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0,k4_filter_0(sK3,X0,X1)),X1)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(backward_subsumption_resolution,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_780,c_555]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1832,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0_53,k4_filter_0(sK3,X0_53,X1_53)),X1_53)
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_808]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2219,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0_53,k4_filter_0(sK3,X0_53,X1_53)),X1_53) = iProver_top
% 11.38/2.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1832]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_16,plain,
% 11.38/2.00      ( ~ r3_lattices(X0,k4_lattices(X0,X1,X2),X3)
% 11.38/2.00      | r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.38/2.00      | ~ v4_lattice3(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_496,plain,
% 11.38/2.00      ( ~ r3_lattices(X0,k4_lattices(X0,X1,X2),X3)
% 11.38/2.00      | r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0)
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_497,plain,
% 11.38/2.00      ( ~ r3_lattices(sK3,k4_lattices(sK3,X0,X1),X2)
% 11.38/2.00      | r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3)
% 11.38/2.00      | ~ v10_lattices(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_496]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_501,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
% 11.38/2.00      | ~ r3_lattices(sK3,k4_lattices(sK3,X0,X1),X2) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_497,c_31,c_30,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_502,plain,
% 11.38/2.00      ( ~ r3_lattices(sK3,k4_lattices(sK3,X0,X1),X2)
% 11.38/2.00      | r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_501]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1837,plain,
% 11.38/2.00      ( ~ r3_lattices(sK3,k4_lattices(sK3,X0_53,X1_53),X2_53)
% 11.38/2.00      | r2_hidden(X1_53,a_3_6_lattice3(sK3,X0_53,X2_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_502]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2214,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0_53,X1_53),X2_53) != iProver_top
% 11.38/2.00      | r2_hidden(X1_53,a_3_6_lattice3(sK3,X0_53,X2_53)) = iProver_top
% 11.38/2.00      | m1_subset_1(X2_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1837]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3076,plain,
% 11.38/2.00      ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) = iProver_top
% 11.38/2.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_2219,c_2214]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3008,plain,
% 11.38/2.00      ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_1832,c_1837]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1833,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(k4_filter_0(sK3,X1_53,X0_53),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_780]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2218,plain,
% 11.38/2.00      ( m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) = iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2378,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2218]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2451,plain,
% 11.38/2.00      ( ~ r3_lattices(sK3,k4_lattices(sK3,X0_53,k4_filter_0(sK3,X0_53,X1_53)),X1_53)
% 11.38/2.00      | r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1837]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3079,plain,
% 11.38/2.00      ( ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_3008,c_1832,c_2378,c_2451]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3080,plain,
% 11.38/2.00      ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_3079]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3081,plain,
% 11.38/2.00      ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) = iProver_top
% 11.38/2.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_3080]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4151,plain,
% 11.38/2.00      ( m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) = iProver_top ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_3076,c_3081]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4152,plain,
% 11.38/2.00      ( r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) = iProver_top
% 11.38/2.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_4151]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_18,plain,
% 11.38/2.00      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | ~ v4_lattice3(X1)
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | ~ v10_lattices(X1)
% 11.38/2.00      | sK2(X0,X1,X2,X3) = X0 ),
% 11.38/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_424,plain,
% 11.38/2.00      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | ~ v10_lattices(X1)
% 11.38/2.00      | sK2(X0,X1,X2,X3) = X0
% 11.38/2.00      | sK3 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_425,plain,
% 11.38/2.00      ( ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3)
% 11.38/2.00      | ~ v10_lattices(sK3)
% 11.38/2.00      | sK2(X0,sK3,X1,X2) = X0 ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_424]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_429,plain,
% 11.38/2.00      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
% 11.38/2.00      | sK2(X0,sK3,X1,X2) = X0 ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_425,c_31,c_30,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_430,plain,
% 11.38/2.00      ( ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | sK2(X0,sK3,X1,X2) = X0 ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_429]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1840,plain,
% 11.38/2.00      ( ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | sK2(X0_53,sK3,X1_53,X2_53) = X0_53 ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_430]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2211,plain,
% 11.38/2.00      ( sK2(X0_53,sK3,X1_53,X2_53) = X0_53
% 11.38/2.00      | r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53)) != iProver_top
% 11.38/2.00      | m1_subset_1(X2_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1840]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4158,plain,
% 11.38/2.00      ( sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53) = k4_filter_0(sK3,X0_53,X1_53)
% 11.38/2.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_4152,c_2211]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4302,plain,
% 11.38/2.00      ( sK2(k4_filter_0(sK3,X0_53,sK5),sK3,X0_53,sK5) = k4_filter_0(sK3,X0_53,sK5)
% 11.38/2.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_2208,c_4158]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4357,plain,
% 11.38/2.00      ( sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5) = k4_filter_0(sK3,sK4,sK5)
% 11.38/2.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_4302]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2823,plain,
% 11.38/2.00      ( k4_filter_0(sK3,X0_53,X1_53) = k4_filter_0(sK3,X0_53,X1_53) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1846]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4886,plain,
% 11.38/2.00      ( k4_filter_0(sK3,sK4,sK5) = k4_filter_0(sK3,sK4,sK5) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_2823]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2593,plain,
% 11.38/2.00      ( ~ r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ r2_hidden(k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3))
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,X1_53)) = k4_filter_0(sK3,X0_53,X1_53) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1839]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_5039,plain,
% 11.38/2.00      ( ~ r4_lattice3(sK3,k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
% 11.38/2.00      | ~ r2_hidden(k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,sK4,sK5),u1_struct_0(sK3))
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) = k4_filter_0(sK3,sK4,sK5) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_2593]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_6303,plain,
% 11.38/2.00      ( ~ r3_lattices(sK3,k4_lattices(sK3,sK4,k4_filter_0(sK3,sK4,sK5)),sK5)
% 11.38/2.00      | r2_hidden(k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,sK4,sK5),u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_2451]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_8433,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,sK4,k4_filter_0(sK3,sK4,sK5)),sK5)
% 11.38/2.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1832]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_15849,plain,
% 11.38/2.00      ( m1_subset_1(k4_filter_0(sK3,sK4,sK5),u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1833]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2774,plain,
% 11.38/2.00      ( X0_53 != X1_53
% 11.38/2.00      | k15_lattice3(sK3,X0_54) != X1_53
% 11.38/2.00      | k15_lattice3(sK3,X0_54) = X0_53 ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1848]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3686,plain,
% 11.38/2.00      ( X0_53 != k4_filter_0(sK3,X1_53,X2_53)
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,X1_53,X3_53)) = X0_53
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,X1_53,X3_53)) != k4_filter_0(sK3,X1_53,X2_53) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_2774]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4917,plain,
% 11.38/2.00      ( sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53) != k4_filter_0(sK3,X0_53,X1_53)
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,X2_53)) = sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53)
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,X2_53)) != k4_filter_0(sK3,X0_53,X1_53) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_3686]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_19954,plain,
% 11.38/2.00      ( sK2(k4_filter_0(sK3,X0_53,sK5),sK3,X0_53,sK5) != k4_filter_0(sK3,X0_53,sK5)
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,sK5)) = sK2(k4_filter_0(sK3,X0_53,sK5),sK3,X0_53,sK5)
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,X0_53,sK5)) != k4_filter_0(sK3,X0_53,sK5) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_4917]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_19955,plain,
% 11.38/2.00      ( sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5) != k4_filter_0(sK3,sK4,sK5)
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) = sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5)
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) != k4_filter_0(sK3,sK4,sK5) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_19954]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3784,plain,
% 11.38/2.00      ( X0_53 != X1_53
% 11.38/2.00      | k4_filter_0(sK3,X2_53,X3_53) != X1_53
% 11.38/2.00      | k4_filter_0(sK3,X2_53,X3_53) = X0_53 ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1848]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_6644,plain,
% 11.38/2.00      ( X0_53 != k4_filter_0(sK3,X1_53,X2_53)
% 11.38/2.00      | k4_filter_0(sK3,X1_53,X2_53) = X0_53
% 11.38/2.00      | k4_filter_0(sK3,X1_53,X2_53) != k4_filter_0(sK3,X1_53,X2_53) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_3784]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_9134,plain,
% 11.38/2.00      ( sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53) != k4_filter_0(sK3,X0_53,X1_53)
% 11.38/2.00      | k4_filter_0(sK3,X0_53,X1_53) = sK2(k4_filter_0(sK3,X0_53,X1_53),sK3,X0_53,X1_53)
% 11.38/2.00      | k4_filter_0(sK3,X0_53,X1_53) != k4_filter_0(sK3,X0_53,X1_53) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_6644]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_20767,plain,
% 11.38/2.00      ( sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5) != k4_filter_0(sK3,sK4,sK5)
% 11.38/2.00      | k4_filter_0(sK3,sK4,sK5) = sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5)
% 11.38/2.00      | k4_filter_0(sK3,sK4,sK5) != k4_filter_0(sK3,sK4,sK5) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_9134]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2505,plain,
% 11.38/2.00      ( k4_filter_0(sK3,sK4,sK5) != X0_53
% 11.38/2.00      | k4_filter_0(sK3,sK4,sK5) = k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5))
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) != X0_53 ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1848]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4603,plain,
% 11.38/2.00      ( k4_filter_0(sK3,sK4,sK5) != sK2(k4_filter_0(sK3,sK4,X0_53),sK3,sK4,sK5)
% 11.38/2.00      | k4_filter_0(sK3,sK4,sK5) = k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5))
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) != sK2(k4_filter_0(sK3,sK4,X0_53),sK3,sK4,sK5) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_2505]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_20768,plain,
% 11.38/2.00      ( k4_filter_0(sK3,sK4,sK5) != sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5)
% 11.38/2.00      | k4_filter_0(sK3,sK4,sK5) = k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5))
% 11.38/2.00      | k15_lattice3(sK3,a_3_6_lattice3(sK3,sK4,sK5)) != sK2(k4_filter_0(sK3,sK4,sK5),sK3,sK4,sK5) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_4603]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30601,plain,
% 11.38/2.00      ( ~ r4_lattice3(sK3,k4_filter_0(sK3,sK4,sK5),a_3_6_lattice3(sK3,sK4,sK5)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_30481,c_27,c_36,c_26,c_1844,c_4357,c_4886,c_5039,
% 11.38/2.00                 c_6303,c_8433,c_15849,c_19955,c_20767,c_20768]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_5204,plain,
% 11.38/2.00      ( ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | X0_53 = sK2(X0_53,sK3,X1_53,X2_53) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_2865,c_1840]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1849,plain,
% 11.38/2.00      ( ~ r3_lattices(X0_52,X0_53,X1_53)
% 11.38/2.00      | r3_lattices(X0_52,X2_53,X3_53)
% 11.38/2.00      | X2_53 != X0_53
% 11.38/2.00      | X3_53 != X1_53 ),
% 11.38/2.00      theory(equality) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_4037,plain,
% 11.38/2.00      ( ~ r3_lattices(X0_52,X0_53,X1_53)
% 11.38/2.00      | r3_lattices(X0_52,X2_53,X1_53)
% 11.38/2.00      | X2_53 != X0_53 ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_1849,c_1846]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_5505,plain,
% 11.38/2.00      ( r3_lattices(X0_52,X0_53,X1_53)
% 11.38/2.00      | ~ r3_lattices(X0_52,sK2(X0_53,sK3,X2_53,X3_53),X1_53)
% 11.38/2.00      | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X2_53,X3_53))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X3_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_5204,c_4037]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_9,plain,
% 11.38/2.00      ( r3_lattices(X0,X1,k4_filter_0(X0,X2,X3))
% 11.38/2.00      | ~ r3_lattices(X0,k4_lattices(X0,X2,X1),X3)
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(X0,X2,X3),u1_struct_0(X0))
% 11.38/2.00      | ~ v3_filter_0(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_573,plain,
% 11.38/2.00      ( r3_lattices(X0,X1,k4_filter_0(X0,X2,X3))
% 11.38/2.00      | ~ r3_lattices(X0,k4_lattices(X0,X2,X1),X3)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(X0,X2,X3),u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0)
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_574,plain,
% 11.38/2.00      ( r3_lattices(sK3,X0,k4_filter_0(sK3,X1,X2))
% 11.38/2.00      | ~ r3_lattices(sK3,k4_lattices(sK3,X1,X0),X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X1,X2),u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3)
% 11.38/2.00      | ~ v10_lattices(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_573]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_578,plain,
% 11.38/2.00      ( ~ m1_subset_1(k4_filter_0(sK3,X1,X2),u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ r3_lattices(sK3,k4_lattices(sK3,X1,X0),X2)
% 11.38/2.00      | r3_lattices(sK3,X0,k4_filter_0(sK3,X1,X2)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_574,c_31,c_30,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_579,plain,
% 11.38/2.00      ( r3_lattices(sK3,X0,k4_filter_0(sK3,X1,X2))
% 11.38/2.00      | ~ r3_lattices(sK3,k4_lattices(sK3,X1,X0),X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X1,X2),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_578]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_809,plain,
% 11.38/2.00      ( r3_lattices(sK3,X0,k4_filter_0(sK3,X1,X2))
% 11.38/2.00      | ~ r3_lattices(sK3,k4_lattices(sK3,X1,X0),X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(backward_subsumption_resolution,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_780,c_579]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1831,plain,
% 11.38/2.00      ( r3_lattices(sK3,X0_53,k4_filter_0(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ r3_lattices(sK3,k4_lattices(sK3,X1_53,X0_53),X2_53)
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_809]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_17,plain,
% 11.38/2.00      ( r3_lattices(X0,k4_lattices(X0,X1,sK2(X2,X0,X1,X3)),X3)
% 11.38/2.00      | ~ r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.38/2.00      | ~ v4_lattice3(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_472,plain,
% 11.38/2.00      ( r3_lattices(X0,k4_lattices(X0,X1,sK2(X2,X0,X1,X3)),X3)
% 11.38/2.00      | ~ r2_hidden(X2,a_3_6_lattice3(X0,X1,X3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0)
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_473,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0,sK2(X1,sK3,X0,X2)),X2)
% 11.38/2.00      | ~ r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3)
% 11.38/2.00      | ~ v10_lattices(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_472]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_477,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
% 11.38/2.00      | r3_lattices(sK3,k4_lattices(sK3,X0,sK2(X1,sK3,X0,X2)),X2) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_473,c_31,c_30,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_478,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0,sK2(X1,sK3,X0,X2)),X2)
% 11.38/2.00      | ~ r2_hidden(X1,a_3_6_lattice3(sK3,X0,X2))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_477]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1838,plain,
% 11.38/2.00      ( r3_lattices(sK3,k4_lattices(sK3,X0_53,sK2(X1_53,sK3,X0_53,X2_53)),X2_53)
% 11.38/2.00      | ~ r2_hidden(X1_53,a_3_6_lattice3(sK3,X0_53,X2_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_478]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3341,plain,
% 11.38/2.00      ( r3_lattices(sK3,sK2(X0_53,sK3,X1_53,X2_53),k4_filter_0(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(sK2(X0_53,sK3,X1_53,X2_53),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_1831,c_1838]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_19,plain,
% 11.38/2.00      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
% 11.38/2.00      | ~ v4_lattice3(X1)
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | ~ v10_lattices(X1) ),
% 11.38/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_400,plain,
% 11.38/2.00      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | ~ v10_lattices(X1)
% 11.38/2.00      | sK3 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_401,plain,
% 11.38/2.00      ( ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(sK2(X0,sK3,X1,X2),u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3)
% 11.38/2.00      | ~ v10_lattices(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_400]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_405,plain,
% 11.38/2.00      ( m1_subset_1(sK2(X0,sK3,X1,X2),u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_401,c_31,c_30,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_406,plain,
% 11.38/2.00      ( ~ r2_hidden(X0,a_3_6_lattice3(sK3,X1,X2))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(sK2(X0,sK3,X1,X2),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_405]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1841,plain,
% 11.38/2.00      ( ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(sK2(X0_53,sK3,X1_53,X2_53),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_406]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3574,plain,
% 11.38/2.00      ( ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
% 11.38/2.00      | r3_lattices(sK3,sK2(X0_53,sK3,X1_53,X2_53),k4_filter_0(sK3,X1_53,X2_53)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_3341,c_1841]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3575,plain,
% 11.38/2.00      ( r3_lattices(sK3,sK2(X0_53,sK3,X1_53,X2_53),k4_filter_0(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_3574]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_6193,plain,
% 11.38/2.00      ( r3_lattices(sK3,X0_53,k4_filter_0(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ r2_hidden(X0_53,a_3_6_lattice3(sK3,X1_53,X2_53))
% 11.38/2.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_5505,c_3575]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_0,plain,
% 11.38/2.00      ( ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0)
% 11.38/2.00      | v9_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_5,plain,
% 11.38/2.00      ( r1_lattices(X0,X1,X2)
% 11.38/2.00      | ~ r3_lattices(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ v6_lattices(X0)
% 11.38/2.00      | ~ v8_lattices(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v9_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_320,plain,
% 11.38/2.00      ( r1_lattices(X0,X1,X2)
% 11.38/2.00      | ~ r3_lattices(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ v6_lattices(X0)
% 11.38/2.00      | ~ v8_lattices(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_0,c_5]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2,plain,
% 11.38/2.00      ( v6_lattices(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1,plain,
% 11.38/2.00      ( v8_lattices(X0)
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_324,plain,
% 11.38/2.00      ( r1_lattices(X0,X1,X2)
% 11.38/2.00      | ~ r3_lattices(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ v10_lattices(X0) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_320,c_2,c_1]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_750,plain,
% 11.38/2.00      ( r1_lattices(X0,X1,X2)
% 11.38/2.00      | ~ r3_lattices(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_324,c_24]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_751,plain,
% 11.38/2.00      ( r1_lattices(sK3,X0,X1)
% 11.38/2.00      | ~ r3_lattices(sK3,X0,X1)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3)
% 11.38/2.00      | v2_struct_0(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_750]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_755,plain,
% 11.38/2.00      ( r1_lattices(sK3,X0,X1)
% 11.38/2.00      | ~ r3_lattices(sK3,X0,X1)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_751,c_31,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_12,plain,
% 11.38/2.00      ( r4_lattice3(X0,X1,X2)
% 11.38/2.00      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_25,negated_conjecture,
% 11.38/2.00      ( ~ v2_struct_0(sK3) ),
% 11.38/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_886,plain,
% 11.38/2.00      ( r4_lattice3(X0,X1,X2)
% 11.38/2.00      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_887,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_886]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_891,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 11.38/2.00      | r4_lattice3(sK3,X0,X1) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_887,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_892,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_891]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_947,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | ~ r3_lattices(sK3,X2,X3)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 11.38/2.00      | X0 != X3
% 11.38/2.00      | sK1(sK3,X0,X1) != X2
% 11.38/2.00      | sK3 != sK3 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_755,c_892]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_948,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | ~ r3_lattices(sK3,sK1(sK3,X0,X1),X0)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_947]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_14,plain,
% 11.38/2.00      ( r4_lattice3(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_844,plain,
% 11.38/2.00      ( r4_lattice3(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_845,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_844]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_952,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ r3_lattices(sK3,sK1(sK3,X0,X1),X0)
% 11.38/2.00      | r4_lattice3(sK3,X0,X1) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_948,c_28,c_845]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_953,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | ~ r3_lattices(sK3,sK1(sK3,X0,X1),X0)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_952]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1827,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0_53,X0_54)
% 11.38/2.00      | ~ r3_lattices(sK3,sK1(sK3,X0_53,X0_54),X0_53)
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_953]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_6211,plain,
% 11.38/2.00      ( r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54)
% 11.38/2.00      | ~ r2_hidden(sK1(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_6193,c_1827]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30023,plain,
% 11.38/2.00      ( ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ r2_hidden(sK1(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_6211,c_2378]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30024,plain,
% 11.38/2.00      ( r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54)
% 11.38/2.00      | ~ r2_hidden(sK1(sK3,k4_filter_0(sK3,X0_53,X1_53),X0_54),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_30023]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_13,plain,
% 11.38/2.00      ( r4_lattice3(X0,X1,X2)
% 11.38/2.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_865,plain,
% 11.38/2.00      ( r4_lattice3(X0,X1,X2)
% 11.38/2.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | sK3 != X0 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_866,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | r2_hidden(sK1(sK3,X0,X1),X1)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | ~ l3_lattices(sK3) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_865]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_870,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.38/2.00      | r2_hidden(sK1(sK3,X0,X1),X1)
% 11.38/2.00      | r4_lattice3(sK3,X0,X1) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_866,c_28]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_871,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0,X1)
% 11.38/2.00      | r2_hidden(sK1(sK3,X0,X1),X1)
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_870]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1829,plain,
% 11.38/2.00      ( r4_lattice3(sK3,X0_53,X0_54)
% 11.38/2.00      | r2_hidden(sK1(sK3,X0_53,X0_54),X0_54)
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_871]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30049,plain,
% 11.38/2.00      ( r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(k4_filter_0(sK3,X0_53,X1_53),u1_struct_0(sK3)) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_30024,c_1829]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30164,plain,
% 11.38/2.00      ( ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_30049,c_2378]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30165,plain,
% 11.38/2.00      ( r4_lattice3(sK3,k4_filter_0(sK3,X0_53,X1_53),a_3_6_lattice3(sK3,X0_53,X1_53))
% 11.38/2.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_30164]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30613,plain,
% 11.38/2.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 11.38/2.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_30601,c_30165]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(contradiction,plain,
% 11.38/2.00      ( $false ),
% 11.38/2.00      inference(minisat,[status(thm)],[c_30613,c_26,c_27]) ).
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.38/2.00  
% 11.38/2.00  ------                               Statistics
% 11.38/2.00  
% 11.38/2.00  ------ Selected
% 11.38/2.00  
% 11.38/2.00  total_time:                             1.157
% 11.38/2.00  
%------------------------------------------------------------------------------

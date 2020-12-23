%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:15 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  291 (2632 expanded)
%              Number of clauses        :  179 ( 667 expanded)
%              Number of leaves         :   26 ( 649 expanded)
%              Depth                    :   28
%              Number of atoms          : 1406 (16018 expanded)
%              Number of equality atoms :  317 (3989 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
              & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),sK9)) != sK9
          | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),sK9)) != sK9 )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
              | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k16_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X1)) != X1
            | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & l3_lattices(sK8)
      & v4_lattice3(sK8)
      & v10_lattices(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,
    ( ( k16_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9
      | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9 )
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l3_lattices(sK8)
    & v4_lattice3(sK8)
    & v10_lattices(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f55,f85,f84])).

fof(f135,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f86])).

fof(f14,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f71,plain,(
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
    inference(rectify,[],[f70])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),X2)
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f71,f72])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f131,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f86])).

fof(f134,plain,(
    l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f86])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f139,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f129,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f75,plain,(
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
    inference(flattening,[],[f74])).

fof(f76,plain,(
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
    inference(rectify,[],[f75])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK5(X0,X1,X2))
        & r4_lattice3(X0,sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK5(X0,X1,X2))
                & r4_lattice3(X0,sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f76,f77])).

fof(f121,plain,(
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
    inference(cnf_transformation,[],[f78])).

fof(f140,plain,(
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
    inference(equality_resolution,[],[f121])).

fof(f133,plain,(
    v4_lattice3(sK8) ),
    inference(cnf_transformation,[],[f86])).

fof(f132,plain,(
    v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f86])).

fof(f4,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f97,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f98,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f104,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f80,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f79])).

fof(f82,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK7(X0)) != k2_lattices(X0,sK7(X0),X1)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,X2,sK6(X0)) != k2_lattices(X0,sK6(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK6(X0),sK7(X0)) != k2_lattices(X0,sK7(X0),sK6(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f80,f82,f81])).

fof(f125,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f95,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f137,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f88])).

fof(f138,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f137])).

fof(f120,plain,(
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
    inference(cnf_transformation,[],[f78])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f116,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f18,axiom,(
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

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f103,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f136,plain,
    ( k16_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9
    | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9 ),
    inference(cnf_transformation,[],[f86])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK2(X0))) != X1
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK1(X0),k1_lattices(X0,sK1(X0),X2)) != sK1(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK1(X0),k1_lattices(X0,sK1(X0),sK2(X0))) != sK1(X0)
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f61,f63,f62])).

fof(f99,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
                  & r2_hidden(sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f67,f68])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_4133,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_30,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK4(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_2013,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK4(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_49])).

cnf(c_2014,plain,
    ( r4_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r2_hidden(sK4(sK8,X0,X1),X1)
    | ~ l3_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_2013])).

cnf(c_46,negated_conjecture,
    ( l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_2018,plain,
    ( r2_hidden(sK4(sK8,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r4_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2014,c_46])).

cnf(c_2019,plain,
    ( r4_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r2_hidden(sK4(sK8,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_2018])).

cnf(c_4116,plain,
    ( r4_lattice3(sK8,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK4(sK8,X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2019])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_4134,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6338,plain,
    ( sK4(sK8,X0,k1_tarski(X1)) = X1
    | r4_lattice3(sK8,X0,k1_tarski(X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4116,c_4134])).

cnf(c_42,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1950,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_49])).

cnf(c_1951,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8))
    | ~ l3_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_1950])).

cnf(c_1955,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1951,c_46])).

cnf(c_36,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_47,negated_conjecture,
    ( v4_lattice3(sK8) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1120,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_47])).

cnf(c_1121,plain,
    ( ~ r4_lattice3(sK8,X0,X1)
    | r1_lattices(sK8,k15_lattice3(sK8,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k15_lattice3(sK8,X1),u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1120])).

cnf(c_48,negated_conjecture,
    ( v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1125,plain,
    ( ~ m1_subset_1(k15_lattice3(sK8,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r1_lattices(sK8,k15_lattice3(sK8,X1),X0)
    | ~ r4_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1121,c_49,c_48,c_46])).

cnf(c_1126,plain,
    ( ~ r4_lattice3(sK8,X0,X1)
    | r1_lattices(sK8,k15_lattice3(sK8,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k15_lattice3(sK8,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_1125])).

cnf(c_2222,plain,
    ( ~ r4_lattice3(sK8,X0,X1)
    | r1_lattices(sK8,k15_lattice3(sK8,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1955,c_1126])).

cnf(c_4110,plain,
    ( r4_lattice3(sK8,X0,X1) != iProver_top
    | r1_lattices(sK8,k15_lattice3(sK8,X1),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2222])).

cnf(c_7,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_22,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v9_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_847,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_22])).

cnf(c_6,plain,
    ( ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_851,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_lattices(X0,X1,X2)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_847,c_22,c_7,c_6])).

cnf(c_852,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(renaming,[status(thm)],[c_851])).

cnf(c_1267,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_852,c_48])).

cnf(c_1268,plain,
    ( ~ r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k2_lattices(sK8,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1267])).

cnf(c_1272,plain,
    ( ~ r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1268,c_49,c_46])).

cnf(c_1273,plain,
    ( ~ r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1272])).

cnf(c_4126,plain,
    ( k2_lattices(sK8,X0,X1) = X0
    | r1_lattices(sK8,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_5446,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0),X1) = k15_lattice3(sK8,X0)
    | r4_lattice3(sK8,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4110,c_4126])).

cnf(c_53,plain,
    ( l3_lattices(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_1952,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) = iProver_top
    | l3_lattices(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(c_10230,plain,
    ( m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r4_lattice3(sK8,X1,X0) != iProver_top
    | k2_lattices(sK8,k15_lattice3(sK8,X0),X1) = k15_lattice3(sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5446,c_53,c_1952])).

cnf(c_10231,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0),X1) = k15_lattice3(sK8,X0)
    | r4_lattice3(sK8,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10230])).

cnf(c_10241,plain,
    ( sK4(sK8,X0,k1_tarski(X1)) = X1
    | k2_lattices(sK8,k15_lattice3(sK8,k1_tarski(X1)),X0) = k15_lattice3(sK8,k1_tarski(X1))
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6338,c_10231])).

cnf(c_15309,plain,
    ( sK4(sK8,sK9,k1_tarski(X0)) = X0
    | k2_lattices(sK8,k15_lattice3(sK8,k1_tarski(X0)),sK9) = k15_lattice3(sK8,k1_tarski(X0)) ),
    inference(superposition,[status(thm)],[c_4133,c_10241])).

cnf(c_4119,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_18,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_770,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_18,c_41])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_2170,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_771,c_49])).

cnf(c_2171,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v6_lattices(sK8)
    | ~ l3_lattices(sK8)
    | k2_lattices(sK8,X0,X1) = k2_lattices(sK8,X1,X0) ),
    inference(unflattening,[status(thm)],[c_2170])).

cnf(c_9,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1345,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_48])).

cnf(c_1346,plain,
    ( v6_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1345])).

cnf(c_156,plain,
    ( v6_lattices(sK8)
    | ~ l3_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1348,plain,
    ( v6_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1346,c_49,c_48,c_46,c_156])).

cnf(c_1870,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_771,c_1348])).

cnf(c_1871,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k2_lattices(sK8,X0,X1) = k2_lattices(sK8,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1870])).

cnf(c_2174,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,X1) = k2_lattices(sK8,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2171,c_49,c_46,c_1871])).

cnf(c_2175,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
    inference(renaming,[status(thm)],[c_2174])).

cnf(c_4120,plain,
    ( k2_lattices(sK8,X0,X1) = k2_lattices(sK8,X1,X0)
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2175])).

cnf(c_4961,plain,
    ( k2_lattices(sK8,X0,sK9) = k2_lattices(sK8,sK9,X0)
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_4120])).

cnf(c_5058,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0),sK9) = k2_lattices(sK8,sK9,k15_lattice3(sK8,X0)) ),
    inference(superposition,[status(thm)],[c_4119,c_4961])).

cnf(c_15346,plain,
    ( sK4(sK8,sK9,k1_tarski(X0)) = X0
    | k2_lattices(sK8,sK9,k15_lattice3(sK8,k1_tarski(X0))) = k15_lattice3(sK8,k1_tarski(X0)) ),
    inference(demodulation,[status(thm)],[c_15309,c_5058])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_4135,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_37,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_295,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37,c_42])).

cnf(c_1081,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_47])).

cnf(c_1082,plain,
    ( r4_lattice3(sK8,k15_lattice3(sK8,X0),X0)
    | ~ l3_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1081])).

cnf(c_1086,plain,
    ( r4_lattice3(sK8,k15_lattice3(sK8,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1082,c_49,c_48,c_46])).

cnf(c_4132,plain,
    ( r4_lattice3(sK8,k15_lattice3(sK8,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_32,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1965,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_49])).

cnf(c_1966,plain,
    ( ~ r4_lattice3(sK8,X0,X1)
    | r1_lattices(sK8,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_1965])).

cnf(c_1970,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r1_lattices(sK8,X2,X0)
    | ~ r4_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1966,c_46])).

cnf(c_1971,plain,
    ( ~ r4_lattice3(sK8,X0,X1)
    | r1_lattices(sK8,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ r2_hidden(X2,X1) ),
    inference(renaming,[status(thm)],[c_1970])).

cnf(c_4118,plain,
    ( r4_lattice3(sK8,X0,X1) != iProver_top
    | r1_lattices(sK8,X2,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_5696,plain,
    ( r4_lattice3(sK8,k15_lattice3(sK8,X0),X1) != iProver_top
    | r1_lattices(sK8,X2,k15_lattice3(sK8,X0)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4119,c_4118])).

cnf(c_9863,plain,
    ( r1_lattices(sK8,X0,k15_lattice3(sK8,X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_5696])).

cnf(c_9891,plain,
    ( k2_lattices(sK8,X0,k15_lattice3(sK8,X1)) = X0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k15_lattice3(sK8,X1),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9863,c_4126])).

cnf(c_10173,plain,
    ( k2_lattices(sK8,X0,k15_lattice3(sK8,X1)) = X0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9891,c_4119])).

cnf(c_10177,plain,
    ( k2_lattices(sK8,sK9,k15_lattice3(sK8,X0)) = sK9
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_10173])).

cnf(c_10350,plain,
    ( k2_lattices(sK8,sK9,k15_lattice3(sK8,k1_tarski(sK9))) = sK9 ),
    inference(superposition,[status(thm)],[c_4135,c_10177])).

cnf(c_15374,plain,
    ( sK4(sK8,sK9,k1_tarski(sK9)) = sK9
    | k15_lattice3(sK8,k1_tarski(sK9)) = sK9 ),
    inference(superposition,[status(thm)],[c_15346,c_10350])).

cnf(c_54,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_43,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X2)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1096,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X2)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k16_lattice3(X0,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_47])).

cnf(c_1097,plain,
    ( ~ r3_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X0,X1)
    | ~ l3_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | k16_lattice3(sK8,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1096])).

cnf(c_1101,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r3_lattice3(sK8,X0,X1)
    | k16_lattice3(sK8,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1097,c_49,c_48,c_46])).

cnf(c_1102,plain,
    ( ~ r3_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X0,X1)
    | k16_lattice3(sK8,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1101])).

cnf(c_4471,plain,
    ( ~ r3_lattice3(sK8,sK9,X0)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK9,X0)
    | k16_lattice3(sK8,X0) = sK9 ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_4887,plain,
    ( ~ r3_lattice3(sK8,sK9,k1_tarski(sK9))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK9,k1_tarski(sK9))
    | k16_lattice3(sK8,k1_tarski(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_4471])).

cnf(c_4889,plain,
    ( k16_lattice3(sK8,k1_tarski(sK9)) = sK9
    | r3_lattice3(sK8,sK9,k1_tarski(sK9)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK9,k1_tarski(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4887])).

cnf(c_4888,plain,
    ( r2_hidden(sK9,k1_tarski(sK9)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4891,plain,
    ( r2_hidden(sK9,k1_tarski(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4888])).

cnf(c_21,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v9_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_879,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(resolution,[status(thm)],[c_7,c_21])).

cnf(c_883,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattices(X0,X1,X2)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_879,c_21,c_7,c_6])).

cnf(c_884,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(renaming,[status(thm)],[c_883])).

cnf(c_1243,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_884,c_48])).

cnf(c_1244,plain,
    ( r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k2_lattices(sK8,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_1243])).

cnf(c_1248,plain,
    ( r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1244,c_49,c_46])).

cnf(c_1249,plain,
    ( r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_1248])).

cnf(c_4491,plain,
    ( r1_lattices(sK8,X0,sK9)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,sK9) != X0 ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_4899,plain,
    ( r1_lattices(sK8,sK9,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | k2_lattices(sK8,sK9,sK9) != sK9 ),
    inference(instantiation,[status(thm)],[c_4491])).

cnf(c_4900,plain,
    ( k2_lattices(sK8,sK9,sK9) != sK9
    | r1_lattices(sK8,sK9,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4899])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_17,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_16,plain,
    ( ~ l2_lattices(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_551,plain,
    ( ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_16,c_4])).

cnf(c_635,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_17,c_551])).

cnf(c_1939,plain,
    ( ~ l3_lattices(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_635,c_49])).

cnf(c_1940,plain,
    ( ~ l3_lattices(sK8)
    | ~ v1_xboole_0(u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1939])).

cnf(c_134,plain,
    ( l2_lattices(sK8)
    | ~ l3_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_137,plain,
    ( ~ l2_lattices(sK8)
    | l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_171,plain,
    ( v2_struct_0(sK8)
    | ~ l1_struct_0(sK8)
    | ~ v1_xboole_0(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1942,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1940,c_49,c_46,c_134,c_137,c_171])).

cnf(c_2263,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK8) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_1942])).

cnf(c_2264,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k6_domain_1(u1_struct_0(sK8),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_2263])).

cnf(c_4109,plain,
    ( k6_domain_1(u1_struct_0(sK8),X0) = k1_tarski(X0)
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2264])).

cnf(c_4633,plain,
    ( k6_domain_1(u1_struct_0(sK8),sK9) = k1_tarski(sK9) ),
    inference(superposition,[status(thm)],[c_4133,c_4109])).

cnf(c_44,negated_conjecture,
    ( k16_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9
    | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_4917,plain,
    ( k16_lattice3(sK8,k1_tarski(sK9)) != sK9
    | k15_lattice3(sK8,k1_tarski(sK9)) != sK9 ),
    inference(demodulation,[status(thm)],[c_4633,c_44])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2188,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_49])).

cnf(c_2189,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v9_lattices(sK8)
    | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
    inference(unflattening,[status(thm)],[c_2188])).

cnf(c_1356,plain,
    ( ~ l3_lattices(X0)
    | v9_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_48])).

cnf(c_1357,plain,
    ( ~ l3_lattices(sK8)
    | v9_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1356])).

cnf(c_165,plain,
    ( ~ l3_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v9_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1359,plain,
    ( v9_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1357,c_49,c_48,c_46,c_165])).

cnf(c_1480,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_1359])).

cnf(c_1481,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
    inference(unflattening,[status(thm)],[c_1480])).

cnf(c_2193,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2189,c_49,c_46,c_1481])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,k1_lattices(sK8,X0,X1)) = X0 ),
    inference(renaming,[status(thm)],[c_2193])).

cnf(c_4122,plain,
    ( k2_lattices(sK8,X0,k1_lattices(sK8,X0,X1)) = X0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2194])).

cnf(c_5218,plain,
    ( k2_lattices(sK8,sK9,k1_lattices(sK8,sK9,X0)) = sK9
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_4122])).

cnf(c_5291,plain,
    ( k2_lattices(sK8,sK9,k1_lattices(sK8,sK9,sK9)) = sK9 ),
    inference(superposition,[status(thm)],[c_4133,c_5218])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_911,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ v9_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | X1 != X2
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_912,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v9_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_930,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_912,c_6,c_9])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_930])).

cnf(c_1368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k1_lattices(sK8,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1367])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k1_lattices(sK8,X0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1368,c_49,c_46])).

cnf(c_4123,plain,
    ( k1_lattices(sK8,X0,X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1372])).

cnf(c_4592,plain,
    ( k1_lattices(sK8,sK9,sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_4133,c_4123])).

cnf(c_5296,plain,
    ( k2_lattices(sK8,sK9,sK9) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_5291,c_4592])).

cnf(c_26,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2103,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_49])).

cnf(c_2104,plain,
    ( r3_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r2_hidden(sK3(sK8,X0,X1),X1)
    | ~ l3_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_2103])).

cnf(c_2108,plain,
    ( r2_hidden(sK3(sK8,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r3_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2104,c_46])).

cnf(c_2109,plain,
    ( r3_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r2_hidden(sK3(sK8,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_2108])).

cnf(c_4112,plain,
    ( r3_lattice3(sK8,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK3(sK8,X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2109])).

cnf(c_5723,plain,
    ( sK3(sK8,X0,k1_tarski(X1)) = X1
    | r3_lattice3(sK8,X0,k1_tarski(X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4112,c_4134])).

cnf(c_4131,plain,
    ( k16_lattice3(sK8,X0) = X1
    | r3_lattice3(sK8,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_5993,plain,
    ( sK3(sK8,X0,k1_tarski(X1)) = X1
    | k16_lattice3(sK8,k1_tarski(X1)) = X0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5723,c_4131])).

cnf(c_14252,plain,
    ( sK3(sK8,X0,k1_tarski(X0)) = X0
    | k16_lattice3(sK8,k1_tarski(X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4135,c_5993])).

cnf(c_14305,plain,
    ( sK3(sK8,sK9,k1_tarski(sK9)) = sK9
    | k16_lattice3(sK8,k1_tarski(sK9)) = sK9 ),
    inference(superposition,[status(thm)],[c_4133,c_14252])).

cnf(c_25,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2124,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_49])).

cnf(c_2125,plain,
    ( r3_lattice3(sK8,X0,X1)
    | ~ r1_lattices(sK8,X0,sK3(sK8,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l3_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_2124])).

cnf(c_2129,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r1_lattices(sK8,X0,sK3(sK8,X0,X1))
    | r3_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2125,c_46])).

cnf(c_2130,plain,
    ( r3_lattice3(sK8,X0,X1)
    | ~ r1_lattices(sK8,X0,sK3(sK8,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_2129])).

cnf(c_4111,plain,
    ( r3_lattice3(sK8,X0,X1) = iProver_top
    | r1_lattices(sK8,X0,sK3(sK8,X0,X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2130])).

cnf(c_14381,plain,
    ( k16_lattice3(sK8,k1_tarski(sK9)) = sK9
    | r3_lattice3(sK8,sK9,k1_tarski(sK9)) = iProver_top
    | r1_lattices(sK8,sK9,sK9) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14305,c_4111])).

cnf(c_16578,plain,
    ( sK4(sK8,sK9,k1_tarski(sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15374,c_54,c_4889,c_4891,c_4900,c_4917,c_5296,c_14381])).

cnf(c_29,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2034,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_49])).

cnf(c_2035,plain,
    ( r4_lattice3(sK8,X0,X1)
    | ~ r1_lattices(sK8,sK4(sK8,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l3_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_2034])).

cnf(c_2039,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r1_lattices(sK8,sK4(sK8,X0,X1),X0)
    | r4_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2035,c_46])).

cnf(c_2040,plain,
    ( r4_lattice3(sK8,X0,X1)
    | ~ r1_lattices(sK8,sK4(sK8,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_2039])).

cnf(c_4115,plain,
    ( r4_lattice3(sK8,X0,X1) = iProver_top
    | r1_lattices(sK8,sK4(sK8,X0,X1),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2040])).

cnf(c_16583,plain,
    ( r4_lattice3(sK8,sK9,k1_tarski(sK9)) = iProver_top
    | r1_lattices(sK8,sK9,sK9) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16578,c_4115])).

cnf(c_16756,plain,
    ( r4_lattice3(sK8,sK9,k1_tarski(sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16583,c_54,c_4900,c_5296])).

cnf(c_16761,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_tarski(sK9)),sK9) = k15_lattice3(sK8,k1_tarski(sK9))
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16756,c_10231])).

cnf(c_16762,plain,
    ( k15_lattice3(sK8,k1_tarski(sK9)) = sK9
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16761,c_5058,c_10350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16762,c_14381,c_5296,c_4917,c_4900,c_4891,c_4889,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.40/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.04  
% 3.40/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/1.04  
% 3.40/1.04  ------  iProver source info
% 3.40/1.04  
% 3.40/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.40/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/1.04  git: non_committed_changes: false
% 3.40/1.04  git: last_make_outside_of_git: false
% 3.40/1.04  
% 3.40/1.04  ------ 
% 3.40/1.04  
% 3.40/1.04  ------ Input Options
% 3.40/1.04  
% 3.40/1.04  --out_options                           all
% 3.40/1.04  --tptp_safe_out                         true
% 3.40/1.04  --problem_path                          ""
% 3.40/1.04  --include_path                          ""
% 3.40/1.04  --clausifier                            res/vclausify_rel
% 3.40/1.04  --clausifier_options                    --mode clausify
% 3.40/1.04  --stdin                                 false
% 3.40/1.04  --stats_out                             all
% 3.40/1.04  
% 3.40/1.04  ------ General Options
% 3.40/1.04  
% 3.40/1.04  --fof                                   false
% 3.40/1.04  --time_out_real                         305.
% 3.40/1.04  --time_out_virtual                      -1.
% 3.40/1.04  --symbol_type_check                     false
% 3.40/1.04  --clausify_out                          false
% 3.40/1.04  --sig_cnt_out                           false
% 3.40/1.04  --trig_cnt_out                          false
% 3.40/1.04  --trig_cnt_out_tolerance                1.
% 3.40/1.04  --trig_cnt_out_sk_spl                   false
% 3.40/1.04  --abstr_cl_out                          false
% 3.40/1.04  
% 3.40/1.04  ------ Global Options
% 3.40/1.04  
% 3.40/1.04  --schedule                              default
% 3.40/1.04  --add_important_lit                     false
% 3.40/1.04  --prop_solver_per_cl                    1000
% 3.40/1.04  --min_unsat_core                        false
% 3.40/1.04  --soft_assumptions                      false
% 3.40/1.04  --soft_lemma_size                       3
% 3.40/1.04  --prop_impl_unit_size                   0
% 3.40/1.04  --prop_impl_unit                        []
% 3.40/1.04  --share_sel_clauses                     true
% 3.40/1.04  --reset_solvers                         false
% 3.40/1.04  --bc_imp_inh                            [conj_cone]
% 3.40/1.04  --conj_cone_tolerance                   3.
% 3.40/1.04  --extra_neg_conj                        none
% 3.40/1.04  --large_theory_mode                     true
% 3.40/1.04  --prolific_symb_bound                   200
% 3.40/1.04  --lt_threshold                          2000
% 3.40/1.04  --clause_weak_htbl                      true
% 3.40/1.04  --gc_record_bc_elim                     false
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing Options
% 3.40/1.04  
% 3.40/1.04  --preprocessing_flag                    true
% 3.40/1.04  --time_out_prep_mult                    0.1
% 3.40/1.04  --splitting_mode                        input
% 3.40/1.04  --splitting_grd                         true
% 3.40/1.04  --splitting_cvd                         false
% 3.40/1.04  --splitting_cvd_svl                     false
% 3.40/1.04  --splitting_nvd                         32
% 3.40/1.04  --sub_typing                            true
% 3.40/1.04  --prep_gs_sim                           true
% 3.40/1.04  --prep_unflatten                        true
% 3.40/1.04  --prep_res_sim                          true
% 3.40/1.04  --prep_upred                            true
% 3.40/1.04  --prep_sem_filter                       exhaustive
% 3.40/1.04  --prep_sem_filter_out                   false
% 3.40/1.04  --pred_elim                             true
% 3.40/1.04  --res_sim_input                         true
% 3.40/1.04  --eq_ax_congr_red                       true
% 3.40/1.04  --pure_diseq_elim                       true
% 3.40/1.04  --brand_transform                       false
% 3.40/1.04  --non_eq_to_eq                          false
% 3.40/1.04  --prep_def_merge                        true
% 3.40/1.04  --prep_def_merge_prop_impl              false
% 3.40/1.04  --prep_def_merge_mbd                    true
% 3.40/1.04  --prep_def_merge_tr_red                 false
% 3.40/1.04  --prep_def_merge_tr_cl                  false
% 3.40/1.04  --smt_preprocessing                     true
% 3.40/1.04  --smt_ac_axioms                         fast
% 3.40/1.04  --preprocessed_out                      false
% 3.40/1.04  --preprocessed_stats                    false
% 3.40/1.04  
% 3.40/1.04  ------ Abstraction refinement Options
% 3.40/1.04  
% 3.40/1.04  --abstr_ref                             []
% 3.40/1.04  --abstr_ref_prep                        false
% 3.40/1.04  --abstr_ref_until_sat                   false
% 3.40/1.04  --abstr_ref_sig_restrict                funpre
% 3.40/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.04  --abstr_ref_under                       []
% 3.40/1.04  
% 3.40/1.04  ------ SAT Options
% 3.40/1.04  
% 3.40/1.04  --sat_mode                              false
% 3.40/1.04  --sat_fm_restart_options                ""
% 3.40/1.04  --sat_gr_def                            false
% 3.40/1.04  --sat_epr_types                         true
% 3.40/1.04  --sat_non_cyclic_types                  false
% 3.40/1.04  --sat_finite_models                     false
% 3.40/1.04  --sat_fm_lemmas                         false
% 3.40/1.04  --sat_fm_prep                           false
% 3.40/1.04  --sat_fm_uc_incr                        true
% 3.40/1.04  --sat_out_model                         small
% 3.40/1.04  --sat_out_clauses                       false
% 3.40/1.04  
% 3.40/1.04  ------ QBF Options
% 3.40/1.04  
% 3.40/1.04  --qbf_mode                              false
% 3.40/1.04  --qbf_elim_univ                         false
% 3.40/1.04  --qbf_dom_inst                          none
% 3.40/1.04  --qbf_dom_pre_inst                      false
% 3.40/1.04  --qbf_sk_in                             false
% 3.40/1.04  --qbf_pred_elim                         true
% 3.40/1.04  --qbf_split                             512
% 3.40/1.04  
% 3.40/1.04  ------ BMC1 Options
% 3.40/1.04  
% 3.40/1.04  --bmc1_incremental                      false
% 3.40/1.04  --bmc1_axioms                           reachable_all
% 3.40/1.04  --bmc1_min_bound                        0
% 3.40/1.04  --bmc1_max_bound                        -1
% 3.40/1.04  --bmc1_max_bound_default                -1
% 3.40/1.04  --bmc1_symbol_reachability              true
% 3.40/1.04  --bmc1_property_lemmas                  false
% 3.40/1.04  --bmc1_k_induction                      false
% 3.40/1.04  --bmc1_non_equiv_states                 false
% 3.40/1.04  --bmc1_deadlock                         false
% 3.40/1.04  --bmc1_ucm                              false
% 3.40/1.04  --bmc1_add_unsat_core                   none
% 3.40/1.04  --bmc1_unsat_core_children              false
% 3.40/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.04  --bmc1_out_stat                         full
% 3.40/1.04  --bmc1_ground_init                      false
% 3.40/1.04  --bmc1_pre_inst_next_state              false
% 3.40/1.04  --bmc1_pre_inst_state                   false
% 3.40/1.04  --bmc1_pre_inst_reach_state             false
% 3.40/1.04  --bmc1_out_unsat_core                   false
% 3.40/1.04  --bmc1_aig_witness_out                  false
% 3.40/1.04  --bmc1_verbose                          false
% 3.40/1.04  --bmc1_dump_clauses_tptp                false
% 3.40/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.04  --bmc1_dump_file                        -
% 3.40/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.04  --bmc1_ucm_extend_mode                  1
% 3.40/1.04  --bmc1_ucm_init_mode                    2
% 3.40/1.04  --bmc1_ucm_cone_mode                    none
% 3.40/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.04  --bmc1_ucm_relax_model                  4
% 3.40/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.04  --bmc1_ucm_layered_model                none
% 3.40/1.04  --bmc1_ucm_max_lemma_size               10
% 3.40/1.04  
% 3.40/1.04  ------ AIG Options
% 3.40/1.04  
% 3.40/1.04  --aig_mode                              false
% 3.40/1.04  
% 3.40/1.04  ------ Instantiation Options
% 3.40/1.04  
% 3.40/1.04  --instantiation_flag                    true
% 3.40/1.04  --inst_sos_flag                         false
% 3.40/1.04  --inst_sos_phase                        true
% 3.40/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.04  --inst_lit_sel_side                     num_symb
% 3.40/1.04  --inst_solver_per_active                1400
% 3.40/1.04  --inst_solver_calls_frac                1.
% 3.40/1.04  --inst_passive_queue_type               priority_queues
% 3.40/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.04  --inst_passive_queues_freq              [25;2]
% 3.40/1.04  --inst_dismatching                      true
% 3.40/1.04  --inst_eager_unprocessed_to_passive     true
% 3.40/1.04  --inst_prop_sim_given                   true
% 3.40/1.04  --inst_prop_sim_new                     false
% 3.40/1.04  --inst_subs_new                         false
% 3.40/1.04  --inst_eq_res_simp                      false
% 3.40/1.04  --inst_subs_given                       false
% 3.40/1.04  --inst_orphan_elimination               true
% 3.40/1.04  --inst_learning_loop_flag               true
% 3.40/1.04  --inst_learning_start                   3000
% 3.40/1.04  --inst_learning_factor                  2
% 3.40/1.04  --inst_start_prop_sim_after_learn       3
% 3.40/1.04  --inst_sel_renew                        solver
% 3.40/1.04  --inst_lit_activity_flag                true
% 3.40/1.04  --inst_restr_to_given                   false
% 3.40/1.04  --inst_activity_threshold               500
% 3.40/1.04  --inst_out_proof                        true
% 3.40/1.04  
% 3.40/1.04  ------ Resolution Options
% 3.40/1.04  
% 3.40/1.04  --resolution_flag                       true
% 3.40/1.04  --res_lit_sel                           adaptive
% 3.40/1.04  --res_lit_sel_side                      none
% 3.40/1.04  --res_ordering                          kbo
% 3.40/1.04  --res_to_prop_solver                    active
% 3.40/1.04  --res_prop_simpl_new                    false
% 3.40/1.04  --res_prop_simpl_given                  true
% 3.40/1.04  --res_passive_queue_type                priority_queues
% 3.40/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.04  --res_passive_queues_freq               [15;5]
% 3.40/1.04  --res_forward_subs                      full
% 3.40/1.04  --res_backward_subs                     full
% 3.40/1.04  --res_forward_subs_resolution           true
% 3.40/1.04  --res_backward_subs_resolution          true
% 3.40/1.04  --res_orphan_elimination                true
% 3.40/1.04  --res_time_limit                        2.
% 3.40/1.04  --res_out_proof                         true
% 3.40/1.04  
% 3.40/1.04  ------ Superposition Options
% 3.40/1.04  
% 3.40/1.04  --superposition_flag                    true
% 3.40/1.04  --sup_passive_queue_type                priority_queues
% 3.40/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.40/1.04  --demod_completeness_check              fast
% 3.40/1.04  --demod_use_ground                      true
% 3.40/1.04  --sup_to_prop_solver                    passive
% 3.40/1.04  --sup_prop_simpl_new                    true
% 3.40/1.04  --sup_prop_simpl_given                  true
% 3.40/1.04  --sup_fun_splitting                     false
% 3.40/1.04  --sup_smt_interval                      50000
% 3.40/1.04  
% 3.40/1.04  ------ Superposition Simplification Setup
% 3.40/1.04  
% 3.40/1.04  --sup_indices_passive                   []
% 3.40/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_full_bw                           [BwDemod]
% 3.40/1.04  --sup_immed_triv                        [TrivRules]
% 3.40/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_immed_bw_main                     []
% 3.40/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.04  
% 3.40/1.04  ------ Combination Options
% 3.40/1.04  
% 3.40/1.04  --comb_res_mult                         3
% 3.40/1.04  --comb_sup_mult                         2
% 3.40/1.04  --comb_inst_mult                        10
% 3.40/1.04  
% 3.40/1.04  ------ Debug Options
% 3.40/1.04  
% 3.40/1.04  --dbg_backtrace                         false
% 3.40/1.04  --dbg_dump_prop_clauses                 false
% 3.40/1.04  --dbg_dump_prop_clauses_file            -
% 3.40/1.04  --dbg_out_stat                          false
% 3.40/1.04  ------ Parsing...
% 3.40/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/1.04  ------ Proving...
% 3.40/1.04  ------ Problem Properties 
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  clauses                                 30
% 3.40/1.04  conjectures                             2
% 3.40/1.04  EPR                                     0
% 3.40/1.04  Horn                                    23
% 3.40/1.04  unary                                   4
% 3.40/1.04  binary                                  4
% 3.40/1.04  lits                                    92
% 3.40/1.04  lits eq                                 19
% 3.40/1.04  fd_pure                                 0
% 3.40/1.04  fd_pseudo                               0
% 3.40/1.04  fd_cond                                 0
% 3.40/1.04  fd_pseudo_cond                          7
% 3.40/1.04  AC symbols                              0
% 3.40/1.04  
% 3.40/1.04  ------ Schedule dynamic 5 is on 
% 3.40/1.04  
% 3.40/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  ------ 
% 3.40/1.04  Current options:
% 3.40/1.04  ------ 
% 3.40/1.04  
% 3.40/1.04  ------ Input Options
% 3.40/1.04  
% 3.40/1.04  --out_options                           all
% 3.40/1.04  --tptp_safe_out                         true
% 3.40/1.04  --problem_path                          ""
% 3.40/1.04  --include_path                          ""
% 3.40/1.04  --clausifier                            res/vclausify_rel
% 3.40/1.04  --clausifier_options                    --mode clausify
% 3.40/1.04  --stdin                                 false
% 3.40/1.04  --stats_out                             all
% 3.40/1.04  
% 3.40/1.04  ------ General Options
% 3.40/1.04  
% 3.40/1.04  --fof                                   false
% 3.40/1.04  --time_out_real                         305.
% 3.40/1.04  --time_out_virtual                      -1.
% 3.40/1.04  --symbol_type_check                     false
% 3.40/1.04  --clausify_out                          false
% 3.40/1.04  --sig_cnt_out                           false
% 3.40/1.04  --trig_cnt_out                          false
% 3.40/1.04  --trig_cnt_out_tolerance                1.
% 3.40/1.04  --trig_cnt_out_sk_spl                   false
% 3.40/1.04  --abstr_cl_out                          false
% 3.40/1.04  
% 3.40/1.04  ------ Global Options
% 3.40/1.04  
% 3.40/1.04  --schedule                              default
% 3.40/1.04  --add_important_lit                     false
% 3.40/1.04  --prop_solver_per_cl                    1000
% 3.40/1.04  --min_unsat_core                        false
% 3.40/1.04  --soft_assumptions                      false
% 3.40/1.04  --soft_lemma_size                       3
% 3.40/1.04  --prop_impl_unit_size                   0
% 3.40/1.04  --prop_impl_unit                        []
% 3.40/1.04  --share_sel_clauses                     true
% 3.40/1.04  --reset_solvers                         false
% 3.40/1.04  --bc_imp_inh                            [conj_cone]
% 3.40/1.04  --conj_cone_tolerance                   3.
% 3.40/1.04  --extra_neg_conj                        none
% 3.40/1.04  --large_theory_mode                     true
% 3.40/1.04  --prolific_symb_bound                   200
% 3.40/1.04  --lt_threshold                          2000
% 3.40/1.04  --clause_weak_htbl                      true
% 3.40/1.04  --gc_record_bc_elim                     false
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing Options
% 3.40/1.04  
% 3.40/1.04  --preprocessing_flag                    true
% 3.40/1.04  --time_out_prep_mult                    0.1
% 3.40/1.04  --splitting_mode                        input
% 3.40/1.04  --splitting_grd                         true
% 3.40/1.04  --splitting_cvd                         false
% 3.40/1.04  --splitting_cvd_svl                     false
% 3.40/1.04  --splitting_nvd                         32
% 3.40/1.04  --sub_typing                            true
% 3.40/1.04  --prep_gs_sim                           true
% 3.40/1.04  --prep_unflatten                        true
% 3.40/1.04  --prep_res_sim                          true
% 3.40/1.04  --prep_upred                            true
% 3.40/1.04  --prep_sem_filter                       exhaustive
% 3.40/1.04  --prep_sem_filter_out                   false
% 3.40/1.04  --pred_elim                             true
% 3.40/1.04  --res_sim_input                         true
% 3.40/1.04  --eq_ax_congr_red                       true
% 3.40/1.04  --pure_diseq_elim                       true
% 3.40/1.04  --brand_transform                       false
% 3.40/1.04  --non_eq_to_eq                          false
% 3.40/1.04  --prep_def_merge                        true
% 3.40/1.04  --prep_def_merge_prop_impl              false
% 3.40/1.04  --prep_def_merge_mbd                    true
% 3.40/1.04  --prep_def_merge_tr_red                 false
% 3.40/1.04  --prep_def_merge_tr_cl                  false
% 3.40/1.04  --smt_preprocessing                     true
% 3.40/1.04  --smt_ac_axioms                         fast
% 3.40/1.04  --preprocessed_out                      false
% 3.40/1.04  --preprocessed_stats                    false
% 3.40/1.04  
% 3.40/1.04  ------ Abstraction refinement Options
% 3.40/1.04  
% 3.40/1.04  --abstr_ref                             []
% 3.40/1.04  --abstr_ref_prep                        false
% 3.40/1.04  --abstr_ref_until_sat                   false
% 3.40/1.04  --abstr_ref_sig_restrict                funpre
% 3.40/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.04  --abstr_ref_under                       []
% 3.40/1.04  
% 3.40/1.04  ------ SAT Options
% 3.40/1.04  
% 3.40/1.04  --sat_mode                              false
% 3.40/1.04  --sat_fm_restart_options                ""
% 3.40/1.04  --sat_gr_def                            false
% 3.40/1.04  --sat_epr_types                         true
% 3.40/1.04  --sat_non_cyclic_types                  false
% 3.40/1.04  --sat_finite_models                     false
% 3.40/1.04  --sat_fm_lemmas                         false
% 3.40/1.04  --sat_fm_prep                           false
% 3.40/1.04  --sat_fm_uc_incr                        true
% 3.40/1.04  --sat_out_model                         small
% 3.40/1.04  --sat_out_clauses                       false
% 3.40/1.04  
% 3.40/1.04  ------ QBF Options
% 3.40/1.04  
% 3.40/1.04  --qbf_mode                              false
% 3.40/1.04  --qbf_elim_univ                         false
% 3.40/1.04  --qbf_dom_inst                          none
% 3.40/1.04  --qbf_dom_pre_inst                      false
% 3.40/1.04  --qbf_sk_in                             false
% 3.40/1.04  --qbf_pred_elim                         true
% 3.40/1.04  --qbf_split                             512
% 3.40/1.04  
% 3.40/1.04  ------ BMC1 Options
% 3.40/1.04  
% 3.40/1.04  --bmc1_incremental                      false
% 3.40/1.04  --bmc1_axioms                           reachable_all
% 3.40/1.04  --bmc1_min_bound                        0
% 3.40/1.04  --bmc1_max_bound                        -1
% 3.40/1.04  --bmc1_max_bound_default                -1
% 3.40/1.04  --bmc1_symbol_reachability              true
% 3.40/1.04  --bmc1_property_lemmas                  false
% 3.40/1.04  --bmc1_k_induction                      false
% 3.40/1.04  --bmc1_non_equiv_states                 false
% 3.40/1.04  --bmc1_deadlock                         false
% 3.40/1.04  --bmc1_ucm                              false
% 3.40/1.04  --bmc1_add_unsat_core                   none
% 3.40/1.04  --bmc1_unsat_core_children              false
% 3.40/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.04  --bmc1_out_stat                         full
% 3.40/1.04  --bmc1_ground_init                      false
% 3.40/1.04  --bmc1_pre_inst_next_state              false
% 3.40/1.04  --bmc1_pre_inst_state                   false
% 3.40/1.04  --bmc1_pre_inst_reach_state             false
% 3.40/1.04  --bmc1_out_unsat_core                   false
% 3.40/1.04  --bmc1_aig_witness_out                  false
% 3.40/1.04  --bmc1_verbose                          false
% 3.40/1.04  --bmc1_dump_clauses_tptp                false
% 3.40/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.04  --bmc1_dump_file                        -
% 3.40/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.04  --bmc1_ucm_extend_mode                  1
% 3.40/1.04  --bmc1_ucm_init_mode                    2
% 3.40/1.04  --bmc1_ucm_cone_mode                    none
% 3.40/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.04  --bmc1_ucm_relax_model                  4
% 3.40/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.04  --bmc1_ucm_layered_model                none
% 3.40/1.04  --bmc1_ucm_max_lemma_size               10
% 3.40/1.04  
% 3.40/1.04  ------ AIG Options
% 3.40/1.04  
% 3.40/1.04  --aig_mode                              false
% 3.40/1.04  
% 3.40/1.04  ------ Instantiation Options
% 3.40/1.04  
% 3.40/1.04  --instantiation_flag                    true
% 3.40/1.04  --inst_sos_flag                         false
% 3.40/1.04  --inst_sos_phase                        true
% 3.40/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.04  --inst_lit_sel_side                     none
% 3.40/1.04  --inst_solver_per_active                1400
% 3.40/1.04  --inst_solver_calls_frac                1.
% 3.40/1.04  --inst_passive_queue_type               priority_queues
% 3.40/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.04  --inst_passive_queues_freq              [25;2]
% 3.40/1.04  --inst_dismatching                      true
% 3.40/1.04  --inst_eager_unprocessed_to_passive     true
% 3.40/1.04  --inst_prop_sim_given                   true
% 3.40/1.04  --inst_prop_sim_new                     false
% 3.40/1.04  --inst_subs_new                         false
% 3.40/1.04  --inst_eq_res_simp                      false
% 3.40/1.04  --inst_subs_given                       false
% 3.40/1.04  --inst_orphan_elimination               true
% 3.40/1.04  --inst_learning_loop_flag               true
% 3.40/1.04  --inst_learning_start                   3000
% 3.40/1.04  --inst_learning_factor                  2
% 3.40/1.04  --inst_start_prop_sim_after_learn       3
% 3.40/1.04  --inst_sel_renew                        solver
% 3.40/1.04  --inst_lit_activity_flag                true
% 3.40/1.04  --inst_restr_to_given                   false
% 3.40/1.04  --inst_activity_threshold               500
% 3.40/1.04  --inst_out_proof                        true
% 3.40/1.04  
% 3.40/1.04  ------ Resolution Options
% 3.40/1.04  
% 3.40/1.04  --resolution_flag                       false
% 3.40/1.04  --res_lit_sel                           adaptive
% 3.40/1.04  --res_lit_sel_side                      none
% 3.40/1.04  --res_ordering                          kbo
% 3.40/1.04  --res_to_prop_solver                    active
% 3.40/1.04  --res_prop_simpl_new                    false
% 3.40/1.04  --res_prop_simpl_given                  true
% 3.40/1.04  --res_passive_queue_type                priority_queues
% 3.40/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.04  --res_passive_queues_freq               [15;5]
% 3.40/1.04  --res_forward_subs                      full
% 3.40/1.04  --res_backward_subs                     full
% 3.40/1.04  --res_forward_subs_resolution           true
% 3.40/1.04  --res_backward_subs_resolution          true
% 3.40/1.04  --res_orphan_elimination                true
% 3.40/1.04  --res_time_limit                        2.
% 3.40/1.04  --res_out_proof                         true
% 3.40/1.04  
% 3.40/1.04  ------ Superposition Options
% 3.40/1.04  
% 3.40/1.04  --superposition_flag                    true
% 3.40/1.04  --sup_passive_queue_type                priority_queues
% 3.40/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.40/1.04  --demod_completeness_check              fast
% 3.40/1.04  --demod_use_ground                      true
% 3.40/1.04  --sup_to_prop_solver                    passive
% 3.40/1.04  --sup_prop_simpl_new                    true
% 3.40/1.04  --sup_prop_simpl_given                  true
% 3.40/1.04  --sup_fun_splitting                     false
% 3.40/1.04  --sup_smt_interval                      50000
% 3.40/1.04  
% 3.40/1.04  ------ Superposition Simplification Setup
% 3.40/1.04  
% 3.40/1.04  --sup_indices_passive                   []
% 3.40/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_full_bw                           [BwDemod]
% 3.40/1.04  --sup_immed_triv                        [TrivRules]
% 3.40/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_immed_bw_main                     []
% 3.40/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.04  
% 3.40/1.04  ------ Combination Options
% 3.40/1.04  
% 3.40/1.04  --comb_res_mult                         3
% 3.40/1.04  --comb_sup_mult                         2
% 3.40/1.04  --comb_inst_mult                        10
% 3.40/1.04  
% 3.40/1.04  ------ Debug Options
% 3.40/1.04  
% 3.40/1.04  --dbg_backtrace                         false
% 3.40/1.04  --dbg_dump_prop_clauses                 false
% 3.40/1.04  --dbg_dump_prop_clauses_file            -
% 3.40/1.04  --dbg_out_stat                          false
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  ------ Proving...
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  % SZS status Theorem for theBenchmark.p
% 3.40/1.04  
% 3.40/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/1.04  
% 3.40/1.04  fof(f19,conjecture,(
% 3.40/1.04    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f20,negated_conjecture,(
% 3.40/1.04    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 3.40/1.04    inference(negated_conjecture,[],[f19])).
% 3.40/1.04  
% 3.40/1.04  fof(f54,plain,(
% 3.40/1.04    ? [X0] : (? [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f20])).
% 3.40/1.04  
% 3.40/1.04  fof(f55,plain,(
% 3.40/1.04    ? [X0] : (? [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f54])).
% 3.40/1.04  
% 3.40/1.04  fof(f85,plain,(
% 3.40/1.04    ( ! [X0] : (? [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(X0))) => ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),sK9)) != sK9 | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),sK9)) != sK9) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f84,plain,(
% 3.40/1.04    ? [X0] : (? [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k16_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X1)) != X1 | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X1)) != X1) & m1_subset_1(X1,u1_struct_0(sK8))) & l3_lattices(sK8) & v4_lattice3(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f86,plain,(
% 3.40/1.04    ((k16_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9 | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9) & m1_subset_1(sK9,u1_struct_0(sK8))) & l3_lattices(sK8) & v4_lattice3(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8)),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f55,f85,f84])).
% 3.40/1.04  
% 3.40/1.04  fof(f135,plain,(
% 3.40/1.04    m1_subset_1(sK9,u1_struct_0(sK8))),
% 3.40/1.04    inference(cnf_transformation,[],[f86])).
% 3.40/1.04  
% 3.40/1.04  fof(f14,axiom,(
% 3.40/1.04    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f44,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f14])).
% 3.40/1.04  
% 3.40/1.04  fof(f45,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f44])).
% 3.40/1.04  
% 3.40/1.04  fof(f70,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(nnf_transformation,[],[f45])).
% 3.40/1.04  
% 3.40/1.04  fof(f71,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(rectify,[],[f70])).
% 3.40/1.04  
% 3.40/1.04  fof(f72,plain,(
% 3.40/1.04    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f73,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f71,f72])).
% 3.40/1.04  
% 3.40/1.04  fof(f118,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f73])).
% 3.40/1.04  
% 3.40/1.04  fof(f131,plain,(
% 3.40/1.04    ~v2_struct_0(sK8)),
% 3.40/1.04    inference(cnf_transformation,[],[f86])).
% 3.40/1.04  
% 3.40/1.04  fof(f134,plain,(
% 3.40/1.04    l3_lattices(sK8)),
% 3.40/1.04    inference(cnf_transformation,[],[f86])).
% 3.40/1.04  
% 3.40/1.04  fof(f1,axiom,(
% 3.40/1.04    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f56,plain,(
% 3.40/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.40/1.04    inference(nnf_transformation,[],[f1])).
% 3.40/1.04  
% 3.40/1.04  fof(f57,plain,(
% 3.40/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.40/1.04    inference(rectify,[],[f56])).
% 3.40/1.04  
% 3.40/1.04  fof(f58,plain,(
% 3.40/1.04    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f59,plain,(
% 3.40/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).
% 3.40/1.04  
% 3.40/1.04  fof(f87,plain,(
% 3.40/1.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.40/1.04    inference(cnf_transformation,[],[f59])).
% 3.40/1.04  
% 3.40/1.04  fof(f139,plain,(
% 3.40/1.04    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.40/1.04    inference(equality_resolution,[],[f87])).
% 3.40/1.04  
% 3.40/1.04  fof(f17,axiom,(
% 3.40/1.04    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f50,plain,(
% 3.40/1.04    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f17])).
% 3.40/1.04  
% 3.40/1.04  fof(f51,plain,(
% 3.40/1.04    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f50])).
% 3.40/1.04  
% 3.40/1.04  fof(f129,plain,(
% 3.40/1.04    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f51])).
% 3.40/1.04  
% 3.40/1.04  fof(f15,axiom,(
% 3.40/1.04    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f46,plain,(
% 3.40/1.04    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f15])).
% 3.40/1.04  
% 3.40/1.04  fof(f47,plain,(
% 3.40/1.04    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f46])).
% 3.40/1.04  
% 3.40/1.04  fof(f74,plain,(
% 3.40/1.04    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(nnf_transformation,[],[f47])).
% 3.40/1.04  
% 3.40/1.04  fof(f75,plain,(
% 3.40/1.04    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f74])).
% 3.40/1.04  
% 3.40/1.04  fof(f76,plain,(
% 3.40/1.04    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(rectify,[],[f75])).
% 3.40/1.04  
% 3.40/1.04  fof(f77,plain,(
% 3.40/1.04    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK5(X0,X1,X2)) & r4_lattice3(X0,sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f78,plain,(
% 3.40/1.04    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK5(X0,X1,X2)) & r4_lattice3(X0,sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f76,f77])).
% 3.40/1.04  
% 3.40/1.04  fof(f121,plain,(
% 3.40/1.04    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f78])).
% 3.40/1.04  
% 3.40/1.04  fof(f140,plain,(
% 3.40/1.04    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(equality_resolution,[],[f121])).
% 3.40/1.04  
% 3.40/1.04  fof(f133,plain,(
% 3.40/1.04    v4_lattice3(sK8)),
% 3.40/1.04    inference(cnf_transformation,[],[f86])).
% 3.40/1.04  
% 3.40/1.04  fof(f132,plain,(
% 3.40/1.04    v10_lattices(sK8)),
% 3.40/1.04    inference(cnf_transformation,[],[f86])).
% 3.40/1.04  
% 3.40/1.04  fof(f4,axiom,(
% 3.40/1.04    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f21,plain,(
% 3.40/1.04    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.40/1.04    inference(pure_predicate_removal,[],[f4])).
% 3.40/1.04  
% 3.40/1.04  fof(f26,plain,(
% 3.40/1.04    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.40/1.04    inference(ennf_transformation,[],[f21])).
% 3.40/1.04  
% 3.40/1.04  fof(f27,plain,(
% 3.40/1.04    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.40/1.04    inference(flattening,[],[f26])).
% 3.40/1.04  
% 3.40/1.04  fof(f97,plain,(
% 3.40/1.04    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f27])).
% 3.40/1.04  
% 3.40/1.04  fof(f10,axiom,(
% 3.40/1.04    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f36,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f10])).
% 3.40/1.04  
% 3.40/1.04  fof(f37,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f36])).
% 3.40/1.04  
% 3.40/1.04  fof(f65,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(nnf_transformation,[],[f37])).
% 3.40/1.04  
% 3.40/1.04  fof(f108,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f65])).
% 3.40/1.04  
% 3.40/1.04  fof(f98,plain,(
% 3.40/1.04    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f27])).
% 3.40/1.04  
% 3.40/1.04  fof(f7,axiom,(
% 3.40/1.04    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f31,plain,(
% 3.40/1.04    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.40/1.04    inference(ennf_transformation,[],[f7])).
% 3.40/1.04  
% 3.40/1.04  fof(f104,plain,(
% 3.40/1.04    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f31])).
% 3.40/1.04  
% 3.40/1.04  fof(f16,axiom,(
% 3.40/1.04    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f48,plain,(
% 3.40/1.04    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f16])).
% 3.40/1.04  
% 3.40/1.04  fof(f49,plain,(
% 3.40/1.04    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f48])).
% 3.40/1.04  
% 3.40/1.04  fof(f79,plain,(
% 3.40/1.04    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(nnf_transformation,[],[f49])).
% 3.40/1.04  
% 3.40/1.04  fof(f80,plain,(
% 3.40/1.04    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(rectify,[],[f79])).
% 3.40/1.04  
% 3.40/1.04  fof(f82,plain,(
% 3.40/1.04    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK7(X0)) != k2_lattices(X0,sK7(X0),X1) & m1_subset_1(sK7(X0),u1_struct_0(X0))))) )),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f81,plain,(
% 3.40/1.04    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK6(X0)) != k2_lattices(X0,sK6(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f83,plain,(
% 3.40/1.04    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK6(X0),sK7(X0)) != k2_lattices(X0,sK7(X0),sK6(X0)) & m1_subset_1(sK7(X0),u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f80,f82,f81])).
% 3.40/1.04  
% 3.40/1.04  fof(f125,plain,(
% 3.40/1.04    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f83])).
% 3.40/1.04  
% 3.40/1.04  fof(f95,plain,(
% 3.40/1.04    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f27])).
% 3.40/1.04  
% 3.40/1.04  fof(f88,plain,(
% 3.40/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.40/1.04    inference(cnf_transformation,[],[f59])).
% 3.40/1.04  
% 3.40/1.04  fof(f137,plain,(
% 3.40/1.04    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.40/1.04    inference(equality_resolution,[],[f88])).
% 3.40/1.04  
% 3.40/1.04  fof(f138,plain,(
% 3.40/1.04    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.40/1.04    inference(equality_resolution,[],[f137])).
% 3.40/1.04  
% 3.40/1.04  fof(f120,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f78])).
% 3.40/1.04  
% 3.40/1.04  fof(f141,plain,(
% 3.40/1.04    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(equality_resolution,[],[f120])).
% 3.40/1.04  
% 3.40/1.04  fof(f116,plain,(
% 3.40/1.04    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f73])).
% 3.40/1.04  
% 3.40/1.04  fof(f18,axiom,(
% 3.40/1.04    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f52,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 | (~r3_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f18])).
% 3.40/1.04  
% 3.40/1.04  fof(f53,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 | ~r3_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f52])).
% 3.40/1.04  
% 3.40/1.04  fof(f130,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | ~r3_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f53])).
% 3.40/1.04  
% 3.40/1.04  fof(f109,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f65])).
% 3.40/1.04  
% 3.40/1.04  fof(f3,axiom,(
% 3.40/1.04    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f24,plain,(
% 3.40/1.04    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f3])).
% 3.40/1.04  
% 3.40/1.04  fof(f25,plain,(
% 3.40/1.04    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.40/1.04    inference(flattening,[],[f24])).
% 3.40/1.04  
% 3.40/1.04  fof(f92,plain,(
% 3.40/1.04    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f25])).
% 3.40/1.04  
% 3.40/1.04  fof(f105,plain,(
% 3.40/1.04    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f31])).
% 3.40/1.04  
% 3.40/1.04  fof(f6,axiom,(
% 3.40/1.04    ! [X0] : (l2_lattices(X0) => l1_struct_0(X0))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f30,plain,(
% 3.40/1.04    ! [X0] : (l1_struct_0(X0) | ~l2_lattices(X0))),
% 3.40/1.04    inference(ennf_transformation,[],[f6])).
% 3.40/1.04  
% 3.40/1.04  fof(f103,plain,(
% 3.40/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l2_lattices(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f30])).
% 3.40/1.04  
% 3.40/1.04  fof(f2,axiom,(
% 3.40/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f22,plain,(
% 3.40/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f2])).
% 3.40/1.04  
% 3.40/1.04  fof(f23,plain,(
% 3.40/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f22])).
% 3.40/1.04  
% 3.40/1.04  fof(f91,plain,(
% 3.40/1.04    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f23])).
% 3.40/1.04  
% 3.40/1.04  fof(f136,plain,(
% 3.40/1.04    k16_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9 | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9),
% 3.40/1.04    inference(cnf_transformation,[],[f86])).
% 3.40/1.04  
% 3.40/1.04  fof(f5,axiom,(
% 3.40/1.04    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f28,plain,(
% 3.40/1.04    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f5])).
% 3.40/1.04  
% 3.40/1.04  fof(f29,plain,(
% 3.40/1.04    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f28])).
% 3.40/1.04  
% 3.40/1.04  fof(f60,plain,(
% 3.40/1.04    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(nnf_transformation,[],[f29])).
% 3.40/1.04  
% 3.40/1.04  fof(f61,plain,(
% 3.40/1.04    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(rectify,[],[f60])).
% 3.40/1.04  
% 3.40/1.04  fof(f63,plain,(
% 3.40/1.04    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK2(X0))) != X1 & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f62,plain,(
% 3.40/1.04    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK1(X0),k1_lattices(X0,sK1(X0),X2)) != sK1(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f64,plain,(
% 3.40/1.04    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK1(X0),k1_lattices(X0,sK1(X0),sK2(X0))) != sK1(X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f61,f63,f62])).
% 3.40/1.04  
% 3.40/1.04  fof(f99,plain,(
% 3.40/1.04    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f64])).
% 3.40/1.04  
% 3.40/1.04  fof(f9,axiom,(
% 3.40/1.04    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f34,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f9])).
% 3.40/1.04  
% 3.40/1.04  fof(f35,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f34])).
% 3.40/1.04  
% 3.40/1.04  fof(f107,plain,(
% 3.40/1.04    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f35])).
% 3.40/1.04  
% 3.40/1.04  fof(f13,axiom,(
% 3.40/1.04    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f42,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.40/1.04    inference(ennf_transformation,[],[f13])).
% 3.40/1.04  
% 3.40/1.04  fof(f43,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(flattening,[],[f42])).
% 3.40/1.04  
% 3.40/1.04  fof(f66,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(nnf_transformation,[],[f43])).
% 3.40/1.04  
% 3.40/1.04  fof(f67,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(rectify,[],[f66])).
% 3.40/1.04  
% 3.40/1.04  fof(f68,plain,(
% 3.40/1.04    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f69,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f67,f68])).
% 3.40/1.04  
% 3.40/1.04  fof(f114,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f69])).
% 3.40/1.04  
% 3.40/1.04  fof(f115,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f69])).
% 3.40/1.04  
% 3.40/1.04  fof(f119,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK4(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f73])).
% 3.40/1.04  
% 3.40/1.04  cnf(c_45,negated_conjecture,
% 3.40/1.04      ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 3.40/1.04      inference(cnf_transformation,[],[f135]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4133,plain,
% 3.40/1.04      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_30,plain,
% 3.40/1.04      ( r4_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | r2_hidden(sK4(X0,X1,X2),X2)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f118]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_49,negated_conjecture,
% 3.40/1.04      ( ~ v2_struct_0(sK8) ),
% 3.40/1.04      inference(cnf_transformation,[],[f131]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2013,plain,
% 3.40/1.04      ( r4_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | r2_hidden(sK4(X0,X1,X2),X2)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_30,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2014,plain,
% 3.40/1.04      ( r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | r2_hidden(sK4(sK8,X0,X1),X1)
% 3.40/1.04      | ~ l3_lattices(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_2013]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_46,negated_conjecture,
% 3.40/1.04      ( l3_lattices(sK8) ),
% 3.40/1.04      inference(cnf_transformation,[],[f134]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2018,plain,
% 3.40/1.04      ( r2_hidden(sK4(sK8,X0,X1),X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | r4_lattice3(sK8,X0,X1) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_2014,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2019,plain,
% 3.40/1.04      ( r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | r2_hidden(sK4(sK8,X0,X1),X1) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_2018]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4116,plain,
% 3.40/1.04      ( r4_lattice3(sK8,X0,X1) = iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(sK4(sK8,X0,X1),X1) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2019]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_3,plain,
% 3.40/1.04      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.40/1.04      inference(cnf_transformation,[],[f139]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4134,plain,
% 3.40/1.04      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_6338,plain,
% 3.40/1.04      ( sK4(sK8,X0,k1_tarski(X1)) = X1
% 3.40/1.04      | r4_lattice3(sK8,X0,k1_tarski(X1)) = iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4116,c_4134]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_42,plain,
% 3.40/1.04      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f129]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1950,plain,
% 3.40/1.04      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_42,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1951,plain,
% 3.40/1.04      ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1950]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1955,plain,
% 3.40/1.04      ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1951,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_36,plain,
% 3.40/1.04      ( ~ r4_lattice3(X0,X1,X2)
% 3.40/1.04      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 3.40/1.04      | ~ v4_lattice3(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f140]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_47,negated_conjecture,
% 3.40/1.04      ( v4_lattice3(sK8) ),
% 3.40/1.04      inference(cnf_transformation,[],[f133]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1120,plain,
% 3.40/1.04      ( ~ r4_lattice3(X0,X1,X2)
% 3.40/1.04      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_36,c_47]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1121,plain,
% 3.40/1.04      ( ~ r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | r1_lattices(sK8,k15_lattice3(sK8,X1),X0)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(k15_lattice3(sK8,X1),u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | ~ v10_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1120]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_48,negated_conjecture,
% 3.40/1.04      ( v10_lattices(sK8) ),
% 3.40/1.04      inference(cnf_transformation,[],[f132]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1125,plain,
% 3.40/1.04      ( ~ m1_subset_1(k15_lattice3(sK8,X1),u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | r1_lattices(sK8,k15_lattice3(sK8,X1),X0)
% 3.40/1.04      | ~ r4_lattice3(sK8,X0,X1) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1121,c_49,c_48,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1126,plain,
% 3.40/1.04      ( ~ r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | r1_lattices(sK8,k15_lattice3(sK8,X1),X0)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(k15_lattice3(sK8,X1),u1_struct_0(sK8)) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_1125]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2222,plain,
% 3.40/1.04      ( ~ r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | r1_lattices(sK8,k15_lattice3(sK8,X1),X0)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 3.40/1.04      inference(backward_subsumption_resolution,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1955,c_1126]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4110,plain,
% 3.40/1.04      ( r4_lattice3(sK8,X0,X1) != iProver_top
% 3.40/1.04      | r1_lattices(sK8,k15_lattice3(sK8,X1),X0) = iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2222]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_7,plain,
% 3.40/1.04      ( v8_lattices(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f97]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_22,plain,
% 3.40/1.04      ( ~ r1_lattices(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ v8_lattices(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v9_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) = X1 ),
% 3.40/1.04      inference(cnf_transformation,[],[f108]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_847,plain,
% 3.40/1.04      ( ~ r1_lattices(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | ~ v9_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) = X1 ),
% 3.40/1.04      inference(resolution,[status(thm)],[c_7,c_22]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_6,plain,
% 3.40/1.04      ( ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v9_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f98]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_851,plain,
% 3.40/1.04      ( ~ v10_lattices(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ r1_lattices(X0,X1,X2)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) = X1 ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_847,c_22,c_7,c_6]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_852,plain,
% 3.40/1.04      ( ~ r1_lattices(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) = X1 ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_851]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1267,plain,
% 3.40/1.04      ( ~ r1_lattices(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) = X1
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_852,c_48]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1268,plain,
% 3.40/1.04      ( ~ r1_lattices(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8)
% 3.40/1.04      | k2_lattices(sK8,X0,X1) = X0 ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1267]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1272,plain,
% 3.40/1.04      ( ~ r1_lattices(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X0,X1) = X0 ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1268,c_49,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1273,plain,
% 3.40/1.04      ( ~ r1_lattices(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X0,X1) = X0 ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_1272]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4126,plain,
% 3.40/1.04      ( k2_lattices(sK8,X0,X1) = X0
% 3.40/1.04      | r1_lattices(sK8,X0,X1) != iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5446,plain,
% 3.40/1.04      ( k2_lattices(sK8,k15_lattice3(sK8,X0),X1) = k15_lattice3(sK8,X0)
% 3.40/1.04      | r4_lattice3(sK8,X1,X0) != iProver_top
% 3.40/1.04      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4110,c_4126]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_53,plain,
% 3.40/1.04      ( l3_lattices(sK8) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1952,plain,
% 3.40/1.04      ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) = iProver_top
% 3.40/1.04      | l3_lattices(sK8) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1951]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_10230,plain,
% 3.40/1.04      ( m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r4_lattice3(sK8,X1,X0) != iProver_top
% 3.40/1.04      | k2_lattices(sK8,k15_lattice3(sK8,X0),X1) = k15_lattice3(sK8,X0) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_5446,c_53,c_1952]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_10231,plain,
% 3.40/1.04      ( k2_lattices(sK8,k15_lattice3(sK8,X0),X1) = k15_lattice3(sK8,X0)
% 3.40/1.04      | r4_lattice3(sK8,X1,X0) != iProver_top
% 3.40/1.04      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_10230]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_10241,plain,
% 3.40/1.04      ( sK4(sK8,X0,k1_tarski(X1)) = X1
% 3.40/1.04      | k2_lattices(sK8,k15_lattice3(sK8,k1_tarski(X1)),X0) = k15_lattice3(sK8,k1_tarski(X1))
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_6338,c_10231]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_15309,plain,
% 3.40/1.04      ( sK4(sK8,sK9,k1_tarski(X0)) = X0
% 3.40/1.04      | k2_lattices(sK8,k15_lattice3(sK8,k1_tarski(X0)),sK9) = k15_lattice3(sK8,k1_tarski(X0)) ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4133,c_10241]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4119,plain,
% 3.40/1.04      ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_18,plain,
% 3.40/1.04      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f104]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_41,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.04      | ~ l1_lattices(X1)
% 3.40/1.04      | ~ v6_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f125]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_770,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.04      | ~ v6_lattices(X1)
% 3.40/1.04      | ~ l3_lattices(X3)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | X1 != X3
% 3.40/1.04      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_41]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_771,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.04      | ~ v6_lattices(X1)
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_770]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2170,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.04      | ~ v6_lattices(X1)
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 3.40/1.04      | sK8 != X1 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_771,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2171,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | ~ v6_lattices(sK8)
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | k2_lattices(sK8,X0,X1) = k2_lattices(sK8,X1,X0) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_2170]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_9,plain,
% 3.40/1.04      ( v6_lattices(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f95]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1345,plain,
% 3.40/1.04      ( v6_lattices(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_48]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1346,plain,
% 3.40/1.04      ( v6_lattices(sK8) | ~ l3_lattices(sK8) | v2_struct_0(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1345]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_156,plain,
% 3.40/1.04      ( v6_lattices(sK8)
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | ~ v10_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8) ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_9]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1348,plain,
% 3.40/1.04      ( v6_lattices(sK8) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1346,c_49,c_48,c_46,c_156]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1870,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 3.40/1.04      | sK8 != X1 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_771,c_1348]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1871,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8)
% 3.40/1.04      | k2_lattices(sK8,X0,X1) = k2_lattices(sK8,X1,X0) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1870]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2174,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X0,X1) = k2_lattices(sK8,X1,X0) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_2171,c_49,c_46,c_1871]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2175,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_2174]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4120,plain,
% 3.40/1.04      ( k2_lattices(sK8,X0,X1) = k2_lattices(sK8,X1,X0)
% 3.40/1.04      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2175]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4961,plain,
% 3.40/1.04      ( k2_lattices(sK8,X0,sK9) = k2_lattices(sK8,sK9,X0)
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4133,c_4120]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5058,plain,
% 3.40/1.04      ( k2_lattices(sK8,k15_lattice3(sK8,X0),sK9) = k2_lattices(sK8,sK9,k15_lattice3(sK8,X0)) ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4119,c_4961]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_15346,plain,
% 3.40/1.04      ( sK4(sK8,sK9,k1_tarski(X0)) = X0
% 3.40/1.04      | k2_lattices(sK8,sK9,k15_lattice3(sK8,k1_tarski(X0))) = k15_lattice3(sK8,k1_tarski(X0)) ),
% 3.40/1.04      inference(demodulation,[status(thm)],[c_15309,c_5058]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2,plain,
% 3.40/1.04      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.40/1.04      inference(cnf_transformation,[],[f138]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4135,plain,
% 3.40/1.04      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_37,plain,
% 3.40/1.04      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.40/1.04      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.40/1.04      | ~ v4_lattice3(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f141]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_295,plain,
% 3.40/1.04      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.40/1.04      | ~ v4_lattice3(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_37,c_42]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1081,plain,
% 3.40/1.04      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_295,c_47]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1082,plain,
% 3.40/1.04      ( r4_lattice3(sK8,k15_lattice3(sK8,X0),X0)
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | ~ v10_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1081]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1086,plain,
% 3.40/1.04      ( r4_lattice3(sK8,k15_lattice3(sK8,X0),X0) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1082,c_49,c_48,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4132,plain,
% 3.40/1.04      ( r4_lattice3(sK8,k15_lattice3(sK8,X0),X0) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1086]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_32,plain,
% 3.40/1.04      ( ~ r4_lattice3(X0,X1,X2)
% 3.40/1.04      | r1_lattices(X0,X3,X1)
% 3.40/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ r2_hidden(X3,X2)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f116]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1965,plain,
% 3.40/1.04      ( ~ r4_lattice3(X0,X1,X2)
% 3.40/1.04      | r1_lattices(X0,X3,X1)
% 3.40/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ r2_hidden(X3,X2)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_32,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1966,plain,
% 3.40/1.04      ( ~ r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | r1_lattices(sK8,X2,X0)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.40/1.04      | ~ r2_hidden(X2,X1)
% 3.40/1.04      | ~ l3_lattices(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1965]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1970,plain,
% 3.40/1.04      ( ~ r2_hidden(X2,X1)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | r1_lattices(sK8,X2,X0)
% 3.40/1.04      | ~ r4_lattice3(sK8,X0,X1) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1966,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1971,plain,
% 3.40/1.04      ( ~ r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | r1_lattices(sK8,X2,X0)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.40/1.04      | ~ r2_hidden(X2,X1) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_1970]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4118,plain,
% 3.40/1.04      ( r4_lattice3(sK8,X0,X1) != iProver_top
% 3.40/1.04      | r1_lattices(sK8,X2,X0) = iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(X2,X1) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1971]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5696,plain,
% 3.40/1.04      ( r4_lattice3(sK8,k15_lattice3(sK8,X0),X1) != iProver_top
% 3.40/1.04      | r1_lattices(sK8,X2,k15_lattice3(sK8,X0)) = iProver_top
% 3.40/1.04      | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(X2,X1) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4119,c_4118]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_9863,plain,
% 3.40/1.04      ( r1_lattices(sK8,X0,k15_lattice3(sK8,X1)) = iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(X0,X1) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4132,c_5696]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_9891,plain,
% 3.40/1.04      ( k2_lattices(sK8,X0,k15_lattice3(sK8,X1)) = X0
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | m1_subset_1(k15_lattice3(sK8,X1),u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(X0,X1) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_9863,c_4126]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_10173,plain,
% 3.40/1.04      ( k2_lattices(sK8,X0,k15_lattice3(sK8,X1)) = X0
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(X0,X1) != iProver_top ),
% 3.40/1.04      inference(forward_subsumption_resolution,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_9891,c_4119]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_10177,plain,
% 3.40/1.04      ( k2_lattices(sK8,sK9,k15_lattice3(sK8,X0)) = sK9
% 3.40/1.04      | r2_hidden(sK9,X0) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4133,c_10173]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_10350,plain,
% 3.40/1.04      ( k2_lattices(sK8,sK9,k15_lattice3(sK8,k1_tarski(sK9))) = sK9 ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4135,c_10177]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_15374,plain,
% 3.40/1.04      ( sK4(sK8,sK9,k1_tarski(sK9)) = sK9
% 3.40/1.04      | k15_lattice3(sK8,k1_tarski(sK9)) = sK9 ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_15346,c_10350]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_54,plain,
% 3.40/1.04      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_43,plain,
% 3.40/1.04      ( ~ r3_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ r2_hidden(X1,X2)
% 3.40/1.04      | ~ v4_lattice3(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k16_lattice3(X0,X2) = X1 ),
% 3.40/1.04      inference(cnf_transformation,[],[f130]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1096,plain,
% 3.40/1.04      ( ~ r3_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ r2_hidden(X1,X2)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k16_lattice3(X0,X2) = X1
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_43,c_47]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1097,plain,
% 3.40/1.04      ( ~ r3_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ r2_hidden(X0,X1)
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | ~ v10_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8)
% 3.40/1.04      | k16_lattice3(sK8,X1) = X0 ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1096]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1101,plain,
% 3.40/1.04      ( ~ r2_hidden(X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ r3_lattice3(sK8,X0,X1)
% 3.40/1.04      | k16_lattice3(sK8,X1) = X0 ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1097,c_49,c_48,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1102,plain,
% 3.40/1.04      ( ~ r3_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ r2_hidden(X0,X1)
% 3.40/1.04      | k16_lattice3(sK8,X1) = X0 ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_1101]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4471,plain,
% 3.40/1.04      ( ~ r3_lattice3(sK8,sK9,X0)
% 3.40/1.04      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.40/1.04      | ~ r2_hidden(sK9,X0)
% 3.40/1.04      | k16_lattice3(sK8,X0) = sK9 ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_1102]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4887,plain,
% 3.40/1.04      ( ~ r3_lattice3(sK8,sK9,k1_tarski(sK9))
% 3.40/1.04      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.40/1.04      | ~ r2_hidden(sK9,k1_tarski(sK9))
% 3.40/1.04      | k16_lattice3(sK8,k1_tarski(sK9)) = sK9 ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_4471]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4889,plain,
% 3.40/1.04      ( k16_lattice3(sK8,k1_tarski(sK9)) = sK9
% 3.40/1.04      | r3_lattice3(sK8,sK9,k1_tarski(sK9)) != iProver_top
% 3.40/1.04      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(sK9,k1_tarski(sK9)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_4887]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4888,plain,
% 3.40/1.04      ( r2_hidden(sK9,k1_tarski(sK9)) ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4891,plain,
% 3.40/1.04      ( r2_hidden(sK9,k1_tarski(sK9)) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_4888]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_21,plain,
% 3.40/1.04      ( r1_lattices(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ v8_lattices(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v9_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) != X1 ),
% 3.40/1.04      inference(cnf_transformation,[],[f109]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_879,plain,
% 3.40/1.04      ( r1_lattices(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | ~ v9_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) != X1 ),
% 3.40/1.04      inference(resolution,[status(thm)],[c_7,c_21]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_883,plain,
% 3.40/1.04      ( ~ v10_lattices(X0)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | r1_lattices(X0,X1,X2)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) != X1 ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_879,c_21,c_7,c_6]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_884,plain,
% 3.40/1.04      ( r1_lattices(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | ~ v10_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) != X1 ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_883]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1243,plain,
% 3.40/1.04      ( r1_lattices(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | k2_lattices(X0,X1,X2) != X1
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_884,c_48]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1244,plain,
% 3.40/1.04      ( r1_lattices(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8)
% 3.40/1.04      | k2_lattices(sK8,X0,X1) != X0 ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1243]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1248,plain,
% 3.40/1.04      ( r1_lattices(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X0,X1) != X0 ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1244,c_49,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1249,plain,
% 3.40/1.04      ( r1_lattices(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X0,X1) != X0 ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_1248]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4491,plain,
% 3.40/1.04      ( r1_lattices(sK8,X0,sK9)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X0,sK9) != X0 ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_1249]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4899,plain,
% 3.40/1.04      ( r1_lattices(sK8,sK9,sK9)
% 3.40/1.04      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,sK9,sK9) != sK9 ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_4491]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4900,plain,
% 3.40/1.04      ( k2_lattices(sK8,sK9,sK9) != sK9
% 3.40/1.04      | r1_lattices(sK8,sK9,sK9) = iProver_top
% 3.40/1.04      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_4899]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,X1)
% 3.40/1.04      | v1_xboole_0(X1)
% 3.40/1.04      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f92]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_17,plain,
% 3.40/1.04      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f105]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_16,plain,
% 3.40/1.04      ( ~ l2_lattices(X0) | l1_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f103]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4,plain,
% 3.40/1.04      ( v2_struct_0(X0)
% 3.40/1.04      | ~ l1_struct_0(X0)
% 3.40/1.04      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.40/1.04      inference(cnf_transformation,[],[f91]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_551,plain,
% 3.40/1.04      ( ~ l2_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.40/1.04      inference(resolution,[status(thm)],[c_16,c_4]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_635,plain,
% 3.40/1.04      ( ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.40/1.04      inference(resolution,[status(thm)],[c_17,c_551]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1939,plain,
% 3.40/1.04      ( ~ l3_lattices(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_635,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1940,plain,
% 3.40/1.04      ( ~ l3_lattices(sK8) | ~ v1_xboole_0(u1_struct_0(sK8)) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1939]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_134,plain,
% 3.40/1.04      ( l2_lattices(sK8) | ~ l3_lattices(sK8) ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_17]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_137,plain,
% 3.40/1.04      ( ~ l2_lattices(sK8) | l1_struct_0(sK8) ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_16]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_171,plain,
% 3.40/1.04      ( v2_struct_0(sK8)
% 3.40/1.04      | ~ l1_struct_0(sK8)
% 3.40/1.04      | ~ v1_xboole_0(u1_struct_0(sK8)) ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1942,plain,
% 3.40/1.04      ( ~ v1_xboole_0(u1_struct_0(sK8)) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1940,c_49,c_46,c_134,c_137,c_171]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2263,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,X1)
% 3.40/1.04      | k6_domain_1(X1,X0) = k1_tarski(X0)
% 3.40/1.04      | u1_struct_0(sK8) != X1 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_5,c_1942]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2264,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | k6_domain_1(u1_struct_0(sK8),X0) = k1_tarski(X0) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_2263]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4109,plain,
% 3.40/1.04      ( k6_domain_1(u1_struct_0(sK8),X0) = k1_tarski(X0)
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2264]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4633,plain,
% 3.40/1.04      ( k6_domain_1(u1_struct_0(sK8),sK9) = k1_tarski(sK9) ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4133,c_4109]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_44,negated_conjecture,
% 3.40/1.04      ( k16_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9
% 3.40/1.04      | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK9)) != sK9 ),
% 3.40/1.04      inference(cnf_transformation,[],[f136]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4917,plain,
% 3.40/1.04      ( k16_lattice3(sK8,k1_tarski(sK9)) != sK9
% 3.40/1.04      | k15_lattice3(sK8,k1_tarski(sK9)) != sK9 ),
% 3.40/1.04      inference(demodulation,[status(thm)],[c_4633,c_44]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_15,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | ~ v9_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 3.40/1.04      inference(cnf_transformation,[],[f99]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2188,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | ~ v9_lattices(X1)
% 3.40/1.04      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 3.40/1.04      | sK8 != X1 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2189,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | ~ v9_lattices(sK8)
% 3.40/1.04      | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_2188]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1356,plain,
% 3.40/1.04      ( ~ l3_lattices(X0)
% 3.40/1.04      | v9_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_48]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1357,plain,
% 3.40/1.04      ( ~ l3_lattices(sK8) | v9_lattices(sK8) | v2_struct_0(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1356]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_165,plain,
% 3.40/1.04      ( ~ l3_lattices(sK8)
% 3.40/1.04      | ~ v10_lattices(sK8)
% 3.40/1.04      | v9_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8) ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1359,plain,
% 3.40/1.04      ( v9_lattices(sK8) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1357,c_49,c_48,c_46,c_165]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1480,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 3.40/1.04      | sK8 != X1 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_1359]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1481,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8)
% 3.40/1.04      | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1480]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2193,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_2189,c_49,c_46,c_1481]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2194,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/1.04      | k2_lattices(sK8,X0,k1_lattices(sK8,X0,X1)) = X0 ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_2193]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4122,plain,
% 3.40/1.04      ( k2_lattices(sK8,X0,k1_lattices(sK8,X0,X1)) = X0
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2194]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5218,plain,
% 3.40/1.04      ( k2_lattices(sK8,sK9,k1_lattices(sK8,sK9,X0)) = sK9
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4133,c_4122]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5291,plain,
% 3.40/1.04      ( k2_lattices(sK8,sK9,k1_lattices(sK8,sK9,sK9)) = sK9 ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4133,c_5218]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_20,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ v6_lattices(X1)
% 3.40/1.04      | ~ v8_lattices(X1)
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | ~ v9_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k1_lattices(X1,X0,X0) = X0 ),
% 3.40/1.04      inference(cnf_transformation,[],[f107]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_911,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ v6_lattices(X1)
% 3.40/1.04      | ~ l3_lattices(X2)
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | ~ v10_lattices(X2)
% 3.40/1.04      | ~ v9_lattices(X1)
% 3.40/1.04      | v2_struct_0(X2)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | X1 != X2
% 3.40/1.04      | k1_lattices(X1,X0,X0) = X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_912,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ v6_lattices(X1)
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | ~ v10_lattices(X1)
% 3.40/1.04      | ~ v9_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k1_lattices(X1,X0,X0) = X0 ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_911]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_930,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | ~ v10_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k1_lattices(X1,X0,X0) = X0 ),
% 3.40/1.04      inference(forward_subsumption_resolution,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_912,c_6,c_9]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1367,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.04      | ~ l3_lattices(X1)
% 3.40/1.04      | v2_struct_0(X1)
% 3.40/1.04      | k1_lattices(X1,X0,X0) = X0
% 3.40/1.04      | sK8 != X1 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_48,c_930]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1368,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8)
% 3.40/1.04      | v2_struct_0(sK8)
% 3.40/1.04      | k1_lattices(sK8,X0,X0) = X0 ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_1367]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1372,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | k1_lattices(sK8,X0,X0) = X0 ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1368,c_49,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4123,plain,
% 3.40/1.04      ( k1_lattices(sK8,X0,X0) = X0
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1372]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4592,plain,
% 3.40/1.04      ( k1_lattices(sK8,sK9,sK9) = sK9 ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4133,c_4123]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5296,plain,
% 3.40/1.04      ( k2_lattices(sK8,sK9,sK9) = sK9 ),
% 3.40/1.04      inference(light_normalisation,[status(thm)],[c_5291,c_4592]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_26,plain,
% 3.40/1.04      ( r3_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | r2_hidden(sK3(X0,X1,X2),X2)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f114]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2103,plain,
% 3.40/1.04      ( r3_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | r2_hidden(sK3(X0,X1,X2),X2)
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_26,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2104,plain,
% 3.40/1.04      ( r3_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | r2_hidden(sK3(sK8,X0,X1),X1)
% 3.40/1.04      | ~ l3_lattices(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_2103]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2108,plain,
% 3.40/1.04      ( r2_hidden(sK3(sK8,X0,X1),X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | r3_lattice3(sK8,X0,X1) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_2104,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2109,plain,
% 3.40/1.04      ( r3_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | r2_hidden(sK3(sK8,X0,X1),X1) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_2108]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4112,plain,
% 3.40/1.04      ( r3_lattice3(sK8,X0,X1) = iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(sK3(sK8,X0,X1),X1) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2109]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5723,plain,
% 3.40/1.04      ( sK3(sK8,X0,k1_tarski(X1)) = X1
% 3.40/1.04      | r3_lattice3(sK8,X0,k1_tarski(X1)) = iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4112,c_4134]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4131,plain,
% 3.40/1.04      ( k16_lattice3(sK8,X0) = X1
% 3.40/1.04      | r3_lattice3(sK8,X1,X0) != iProver_top
% 3.40/1.04      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(X1,X0) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1102]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_5993,plain,
% 3.40/1.04      ( sK3(sK8,X0,k1_tarski(X1)) = X1
% 3.40/1.04      | k16_lattice3(sK8,k1_tarski(X1)) = X0
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.40/1.04      | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_5723,c_4131]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_14252,plain,
% 3.40/1.04      ( sK3(sK8,X0,k1_tarski(X0)) = X0
% 3.40/1.04      | k16_lattice3(sK8,k1_tarski(X0)) = X0
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4135,c_5993]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_14305,plain,
% 3.40/1.04      ( sK3(sK8,sK9,k1_tarski(sK9)) = sK9
% 3.40/1.04      | k16_lattice3(sK8,k1_tarski(sK9)) = sK9 ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_4133,c_14252]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_25,plain,
% 3.40/1.04      ( r3_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f115]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2124,plain,
% 3.40/1.04      ( r3_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_25,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2125,plain,
% 3.40/1.04      ( r3_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ r1_lattices(sK8,X0,sK3(sK8,X0,X1))
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_2124]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2129,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ r1_lattices(sK8,X0,sK3(sK8,X0,X1))
% 3.40/1.04      | r3_lattice3(sK8,X0,X1) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_2125,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2130,plain,
% 3.40/1.04      ( r3_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ r1_lattices(sK8,X0,sK3(sK8,X0,X1))
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_2129]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4111,plain,
% 3.40/1.04      ( r3_lattice3(sK8,X0,X1) = iProver_top
% 3.40/1.04      | r1_lattices(sK8,X0,sK3(sK8,X0,X1)) != iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2130]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_14381,plain,
% 3.40/1.04      ( k16_lattice3(sK8,k1_tarski(sK9)) = sK9
% 3.40/1.04      | r3_lattice3(sK8,sK9,k1_tarski(sK9)) = iProver_top
% 3.40/1.04      | r1_lattices(sK8,sK9,sK9) != iProver_top
% 3.40/1.04      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_14305,c_4111]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_16578,plain,
% 3.40/1.04      ( sK4(sK8,sK9,k1_tarski(sK9)) = sK9 ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_15374,c_54,c_4889,c_4891,c_4900,c_4917,c_5296,c_14381]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_29,plain,
% 3.40/1.04      ( r4_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | v2_struct_0(X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f119]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2034,plain,
% 3.40/1.04      ( r4_lattice3(X0,X1,X2)
% 3.40/1.04      | ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
% 3.40/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.04      | ~ l3_lattices(X0)
% 3.40/1.04      | sK8 != X0 ),
% 3.40/1.04      inference(resolution_lifted,[status(thm)],[c_29,c_49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2035,plain,
% 3.40/1.04      ( r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ r1_lattices(sK8,sK4(sK8,X0,X1),X0)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ l3_lattices(sK8) ),
% 3.40/1.04      inference(unflattening,[status(thm)],[c_2034]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2039,plain,
% 3.40/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/1.04      | ~ r1_lattices(sK8,sK4(sK8,X0,X1),X0)
% 3.40/1.04      | r4_lattice3(sK8,X0,X1) ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_2035,c_46]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_2040,plain,
% 3.40/1.04      ( r4_lattice3(sK8,X0,X1)
% 3.40/1.04      | ~ r1_lattices(sK8,sK4(sK8,X0,X1),X0)
% 3.40/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_2039]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4115,plain,
% 3.40/1.04      ( r4_lattice3(sK8,X0,X1) = iProver_top
% 3.40/1.04      | r1_lattices(sK8,sK4(sK8,X0,X1),X0) != iProver_top
% 3.40/1.04      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_2040]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_16583,plain,
% 3.40/1.04      ( r4_lattice3(sK8,sK9,k1_tarski(sK9)) = iProver_top
% 3.40/1.04      | r1_lattices(sK8,sK9,sK9) != iProver_top
% 3.40/1.04      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_16578,c_4115]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_16756,plain,
% 3.40/1.04      ( r4_lattice3(sK8,sK9,k1_tarski(sK9)) = iProver_top ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_16583,c_54,c_4900,c_5296]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_16761,plain,
% 3.40/1.04      ( k2_lattices(sK8,k15_lattice3(sK8,k1_tarski(sK9)),sK9) = k15_lattice3(sK8,k1_tarski(sK9))
% 3.40/1.04      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_16756,c_10231]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_16762,plain,
% 3.40/1.04      ( k15_lattice3(sK8,k1_tarski(sK9)) = sK9
% 3.40/1.04      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
% 3.40/1.04      inference(demodulation,[status(thm)],[c_16761,c_5058,c_10350]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(contradiction,plain,
% 3.40/1.04      ( $false ),
% 3.40/1.04      inference(minisat,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_16762,c_14381,c_5296,c_4917,c_4900,c_4891,c_4889,c_54]) ).
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/1.04  
% 3.40/1.04  ------                               Statistics
% 3.40/1.04  
% 3.40/1.04  ------ General
% 3.40/1.04  
% 3.40/1.04  abstr_ref_over_cycles:                  0
% 3.40/1.04  abstr_ref_under_cycles:                 0
% 3.40/1.04  gc_basic_clause_elim:                   0
% 3.40/1.04  forced_gc_time:                         0
% 3.40/1.04  parsing_time:                           0.02
% 3.40/1.04  unif_index_cands_time:                  0.
% 3.40/1.04  unif_index_add_time:                    0.
% 3.40/1.04  orderings_time:                         0.
% 3.40/1.04  out_proof_time:                         0.018
% 3.40/1.04  total_time:                             0.468
% 3.40/1.04  num_of_symbols:                         67
% 3.40/1.04  num_of_terms:                           15417
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing
% 3.40/1.04  
% 3.40/1.04  num_of_splits:                          0
% 3.40/1.04  num_of_split_atoms:                     0
% 3.40/1.04  num_of_reused_defs:                     0
% 3.40/1.04  num_eq_ax_congr_red:                    69
% 3.40/1.04  num_of_sem_filtered_clauses:            1
% 3.40/1.04  num_of_subtypes:                        0
% 3.40/1.04  monotx_restored_types:                  0
% 3.40/1.04  sat_num_of_epr_types:                   0
% 3.40/1.04  sat_num_of_non_cyclic_types:            0
% 3.40/1.04  sat_guarded_non_collapsed_types:        0
% 3.40/1.04  num_pure_diseq_elim:                    0
% 3.40/1.04  simp_replaced_by:                       0
% 3.40/1.04  res_preprocessed:                       174
% 3.40/1.04  prep_upred:                             0
% 3.40/1.04  prep_unflattend:                        131
% 3.40/1.04  smt_new_axioms:                         0
% 3.40/1.04  pred_elim_cands:                        5
% 3.40/1.04  pred_elim:                              13
% 3.40/1.04  pred_elim_cl:                           19
% 3.40/1.04  pred_elim_cycles:                       23
% 3.40/1.04  merged_defs:                            0
% 3.40/1.04  merged_defs_ncl:                        0
% 3.40/1.04  bin_hyper_res:                          0
% 3.40/1.04  prep_cycles:                            4
% 3.40/1.04  pred_elim_time:                         0.036
% 3.40/1.04  splitting_time:                         0.
% 3.40/1.04  sem_filter_time:                        0.
% 3.40/1.04  monotx_time:                            0.
% 3.40/1.04  subtype_inf_time:                       0.
% 3.40/1.04  
% 3.40/1.04  ------ Problem properties
% 3.40/1.04  
% 3.40/1.04  clauses:                                30
% 3.40/1.04  conjectures:                            2
% 3.40/1.04  epr:                                    0
% 3.40/1.04  horn:                                   23
% 3.40/1.04  ground:                                 2
% 3.40/1.04  unary:                                  4
% 3.40/1.04  binary:                                 4
% 3.40/1.04  lits:                                   92
% 3.40/1.04  lits_eq:                                19
% 3.40/1.04  fd_pure:                                0
% 3.40/1.04  fd_pseudo:                              0
% 3.40/1.04  fd_cond:                                0
% 3.40/1.04  fd_pseudo_cond:                         7
% 3.40/1.04  ac_symbols:                             0
% 3.40/1.04  
% 3.40/1.04  ------ Propositional Solver
% 3.40/1.04  
% 3.40/1.04  prop_solver_calls:                      29
% 3.40/1.04  prop_fast_solver_calls:                 2575
% 3.40/1.04  smt_solver_calls:                       0
% 3.40/1.04  smt_fast_solver_calls:                  0
% 3.40/1.04  prop_num_of_clauses:                    6707
% 3.40/1.04  prop_preprocess_simplified:             14312
% 3.40/1.04  prop_fo_subsumed:                       120
% 3.40/1.04  prop_solver_time:                       0.
% 3.40/1.04  smt_solver_time:                        0.
% 3.40/1.04  smt_fast_solver_time:                   0.
% 3.40/1.04  prop_fast_solver_time:                  0.
% 3.40/1.04  prop_unsat_core_time:                   0.
% 3.40/1.04  
% 3.40/1.04  ------ QBF
% 3.40/1.04  
% 3.40/1.04  qbf_q_res:                              0
% 3.40/1.04  qbf_num_tautologies:                    0
% 3.40/1.04  qbf_prep_cycles:                        0
% 3.40/1.04  
% 3.40/1.04  ------ BMC1
% 3.40/1.04  
% 3.40/1.04  bmc1_current_bound:                     -1
% 3.40/1.04  bmc1_last_solved_bound:                 -1
% 3.40/1.04  bmc1_unsat_core_size:                   -1
% 3.40/1.04  bmc1_unsat_core_parents_size:           -1
% 3.40/1.04  bmc1_merge_next_fun:                    0
% 3.40/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.40/1.04  
% 3.40/1.04  ------ Instantiation
% 3.40/1.04  
% 3.40/1.04  inst_num_of_clauses:                    1399
% 3.40/1.04  inst_num_in_passive:                    381
% 3.40/1.04  inst_num_in_active:                     559
% 3.40/1.04  inst_num_in_unprocessed:                459
% 3.40/1.04  inst_num_of_loops:                      710
% 3.40/1.04  inst_num_of_learning_restarts:          0
% 3.40/1.04  inst_num_moves_active_passive:          149
% 3.40/1.04  inst_lit_activity:                      0
% 3.40/1.04  inst_lit_activity_moves:                1
% 3.40/1.04  inst_num_tautologies:                   0
% 3.40/1.04  inst_num_prop_implied:                  0
% 3.40/1.04  inst_num_existing_simplified:           0
% 3.40/1.04  inst_num_eq_res_simplified:             0
% 3.40/1.04  inst_num_child_elim:                    0
% 3.40/1.04  inst_num_of_dismatching_blockings:      361
% 3.40/1.04  inst_num_of_non_proper_insts:           1207
% 3.40/1.04  inst_num_of_duplicates:                 0
% 3.40/1.04  inst_inst_num_from_inst_to_res:         0
% 3.40/1.04  inst_dismatching_checking_time:         0.
% 3.40/1.04  
% 3.40/1.04  ------ Resolution
% 3.40/1.04  
% 3.40/1.04  res_num_of_clauses:                     0
% 3.40/1.04  res_num_in_passive:                     0
% 3.40/1.04  res_num_in_active:                      0
% 3.40/1.04  res_num_of_loops:                       178
% 3.40/1.04  res_forward_subset_subsumed:            51
% 3.40/1.04  res_backward_subset_subsumed:           0
% 3.40/1.04  res_forward_subsumed:                   0
% 3.40/1.04  res_backward_subsumed:                  0
% 3.40/1.04  res_forward_subsumption_resolution:     5
% 3.40/1.04  res_backward_subsumption_resolution:    1
% 3.40/1.04  res_clause_to_clause_subsumption:       1244
% 3.40/1.04  res_orphan_elimination:                 0
% 3.40/1.04  res_tautology_del:                      27
% 3.40/1.04  res_num_eq_res_simplified:              0
% 3.40/1.04  res_num_sel_changes:                    0
% 3.40/1.04  res_moves_from_active_to_pass:          0
% 3.40/1.04  
% 3.40/1.04  ------ Superposition
% 3.40/1.04  
% 3.40/1.04  sup_time_total:                         0.
% 3.40/1.04  sup_time_generating:                    0.
% 3.40/1.04  sup_time_sim_full:                      0.
% 3.40/1.04  sup_time_sim_immed:                     0.
% 3.40/1.04  
% 3.40/1.04  sup_num_of_clauses:                     313
% 3.40/1.04  sup_num_in_active:                      140
% 3.40/1.04  sup_num_in_passive:                     173
% 3.40/1.04  sup_num_of_loops:                       141
% 3.40/1.04  sup_fw_superposition:                   216
% 3.40/1.04  sup_bw_superposition:                   149
% 3.40/1.04  sup_immediate_simplified:               68
% 3.40/1.04  sup_given_eliminated:                   0
% 3.40/1.05  comparisons_done:                       0
% 3.40/1.05  comparisons_avoided:                    15
% 3.40/1.05  
% 3.40/1.05  ------ Simplifications
% 3.40/1.05  
% 3.40/1.05  
% 3.40/1.05  sim_fw_subset_subsumed:                 15
% 3.40/1.05  sim_bw_subset_subsumed:                 0
% 3.40/1.05  sim_fw_subsumed:                        13
% 3.40/1.05  sim_bw_subsumed:                        1
% 3.40/1.05  sim_fw_subsumption_res:                 18
% 3.40/1.05  sim_bw_subsumption_res:                 0
% 3.40/1.05  sim_tautology_del:                      15
% 3.40/1.05  sim_eq_tautology_del:                   13
% 3.40/1.05  sim_eq_res_simp:                        0
% 3.40/1.05  sim_fw_demodulated:                     8
% 3.40/1.05  sim_bw_demodulated:                     2
% 3.40/1.05  sim_light_normalised:                   35
% 3.40/1.05  sim_joinable_taut:                      0
% 3.40/1.05  sim_joinable_simp:                      0
% 3.40/1.05  sim_ac_normalised:                      0
% 3.40/1.05  sim_smt_subsumption:                    0
% 3.40/1.05  
%------------------------------------------------------------------------------

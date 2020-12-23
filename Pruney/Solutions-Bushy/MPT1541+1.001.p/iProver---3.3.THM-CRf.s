%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1541+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:49 EST 2020

% Result     : Theorem 27.18s
% Output     : CNFRefutation 27.18s
% Verified   : 
% Statistics : Number of formulae       :  365 (4761 expanded)
%              Number of clauses        :  281 (1179 expanded)
%              Number of leaves         :   21 (1522 expanded)
%              Depth                    :   32
%              Number of atoms          : 2188 (63560 expanded)
%              Number of equality atoms :  586 (6424 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   28 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) )
                       => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                          & k11_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                          & k11_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) )
                       => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                          & k11_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                          & k11_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X5,X2)
                                  & r1_orders_2(X0,X5,X1) )
                               => r1_orders_2(X0,X5,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X5,X3)
                            & r1_orders_2(X0,X5,X2)
                            & r1_orders_2(X0,X5,X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X3,X2)
                        | ~ r1_orders_2(X0,X3,X1) )
                      & r2_yellow_0(X0,k2_tarski(X1,X2))
                      & k11_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X5,X3)
                            & r1_orders_2(X0,X5,X2)
                            & r1_orders_2(X0,X5,X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X3,X2)
                        | ~ r1_orders_2(X0,X3,X1) )
                      & r2_yellow_0(X0,k2_tarski(X1,X2))
                      & k11_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( ? [X5] :
              ( ~ r1_orders_2(X0,X5,X3)
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X3,X2)
          | ~ r1_orders_2(X0,X3,X1) )
        & r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ~ sP1(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | sP1(X3,X0,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f19,f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                | k11_lattice3(X0,X1,X2) != X3 )
              & ! [X4] :
                  ( r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r1_orders_2(X0,X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r1_orders_2(X0,X3,X2)
              & r1_orders_2(X0,X3,X1) )
            | sP1(X3,X0,X2,X1) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
              | k11_lattice3(X0,X1,X2) != sK10 )
            & ! [X4] :
                ( r1_orders_2(X0,X4,sK10)
                | ~ r1_orders_2(X0,X4,X2)
                | ~ r1_orders_2(X0,X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_orders_2(X0,sK10,X2)
            & r1_orders_2(X0,sK10,X1) )
          | sP1(sK10,X0,X2,X1) )
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                    | k11_lattice3(X0,X1,X2) != X3 )
                  & ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_orders_2(X0,X4,X2)
                      | ~ r1_orders_2(X0,X4,X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X3,X2)
                  & r1_orders_2(X0,X3,X1) )
                | sP1(X3,X0,X2,X1) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,sK9))
                  | k11_lattice3(X0,X1,sK9) != X3 )
                & ! [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,sK9)
                    | ~ r1_orders_2(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,sK9)
                & r1_orders_2(X0,X3,X1) )
              | sP1(X3,X0,sK9,X1) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | sP1(X3,X0,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(sK8,X2))
                      | k11_lattice3(X0,sK8,X2) != X3 )
                    & ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,sK8)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,sK8) )
                  | sP1(X3,X0,X2,sK8) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                          | k11_lattice3(X0,X1,X2) != X3 )
                        & ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | sP1(X3,X0,X2,X1) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(sK7,k2_tarski(X1,X2))
                        | k11_lattice3(sK7,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(sK7,X4,X3)
                          | ~ r1_orders_2(sK7,X4,X2)
                          | ~ r1_orders_2(sK7,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(sK7)) )
                      & r1_orders_2(sK7,X3,X2)
                      & r1_orders_2(sK7,X3,X1) )
                    | sP1(X3,sK7,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(sK7)) )
              & m1_subset_1(X2,u1_struct_0(sK7)) )
          & m1_subset_1(X1,u1_struct_0(sK7)) )
      & l1_orders_2(sK7)
      & v5_orders_2(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ( ( ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
          | k11_lattice3(sK7,sK8,sK9) != sK10 )
        & ! [X4] :
            ( r1_orders_2(sK7,X4,sK10)
            | ~ r1_orders_2(sK7,X4,sK9)
            | ~ r1_orders_2(sK7,X4,sK8)
            | ~ m1_subset_1(X4,u1_struct_0(sK7)) )
        & r1_orders_2(sK7,sK10,sK9)
        & r1_orders_2(sK7,sK10,sK8) )
      | sP1(sK10,sK7,sK9,sK8) )
    & m1_subset_1(sK10,u1_struct_0(sK7))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l1_orders_2(sK7)
    & v5_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f23,f43,f42,f41,f40])).

fof(f77,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f20,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( k11_lattice3(X0,X1,X2) = X5
          <=> ( ! [X6] :
                  ( r1_orders_2(X0,X6,X5)
                  | ~ r1_orders_2(X0,X6,X2)
                  | ~ r1_orders_2(X0,X6,X1)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1) ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X1)
                  & r1_orders_2(X0,X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X1)
          & r1_orders_2(X0,X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
                & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
                & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
                & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X2,X1))
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f36,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( ? [X5] :
              ( ~ r1_orders_2(X0,X5,X3)
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X3,X2)
          | ~ r1_orders_2(X0,X3,X1) )
        & r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ~ sP1(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ? [X4] :
              ( ~ r1_orders_2(X1,X4,X0)
              & r1_orders_2(X1,X4,X2)
              & r1_orders_2(X1,X4,X3)
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r1_orders_2(X1,X0,X2)
          | ~ r1_orders_2(X1,X0,X3) )
        & r2_yellow_0(X1,k2_tarski(X3,X2))
        & k11_lattice3(X1,X3,X2) = X0 )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK6(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK6(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK6(X0,X1,X2,X3),X3)
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ( ~ r1_orders_2(X1,sK6(X0,X1,X2,X3),X0)
            & r1_orders_2(X1,sK6(X0,X1,X2,X3),X2)
            & r1_orders_2(X1,sK6(X0,X1,X2,X3),X3)
            & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r1_orders_2(X1,X0,X2)
          | ~ r1_orders_2(X1,X0,X3) )
        & r2_yellow_0(X1,k2_tarski(X3,X2))
        & k11_lattice3(X1,X3,X2) = X0 )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X1,k2_tarski(X3,X2))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X4] :
      ( r1_orders_2(sK7,X4,sK10)
      | ~ r1_orders_2(sK7,X4,sK9)
      | ~ r1_orders_2(sK7,X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK7))
      | sP1(sK10,sK7,sK9,sK8) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X1,sK6(X0,X1,X2,X3),X0)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,
    ( r1_orders_2(sK7,sK10,sK8)
    | sP1(sK10,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,
    ( r1_orders_2(sK7,sK10,sK9)
    | sP1(sK10,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK5(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK5(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK5(X0,X1))
              & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X6,X2)
                                  & r1_orders_2(X0,X6,X1) )
                               => r1_orders_2(X0,X6,X5) ) )
                          & r1_orders_2(X0,X5,X2)
                          & r1_orders_2(X0,X5,X1) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f11,f20])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                    & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                    & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                    & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f29])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK5(X0,X1))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X1,X3,X2) = X0
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X2,X1) = X3
      | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK6(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK6(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f47])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f84,plain,
    ( ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10
    | sP1(sK10,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5590,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_68768,plain,
    ( k11_lattice3(sK7,sK8,sK9) != X0_50
    | sK10 != X0_50
    | sK10 = k11_lattice3(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_5590])).

cnf(c_68770,plain,
    ( k11_lattice3(sK7,sK8,sK9) != sK10
    | sK10 = k11_lattice3(sK7,sK8,sK9)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_68768])).

cnf(c_5594,plain,
    ( ~ r1_orders_2(X0_49,X0_50,X1_50)
    | r1_orders_2(X0_49,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_64064,plain,
    ( ~ r1_orders_2(sK7,X0_50,X1_50)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | sK6(sK10,sK7,sK9,sK8) != X0_50
    | sK10 != X1_50 ),
    inference(instantiation,[status(thm)],[c_5594])).

cnf(c_64225,plain,
    ( ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),X0_50)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | sK6(sK10,sK7,sK9,sK8) != sK6(sK10,sK7,sK9,sK8)
    | sK10 != X0_50 ),
    inference(instantiation,[status(thm)],[c_64064])).

cnf(c_64398,plain,
    ( ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),k11_lattice3(sK7,X0_50,X1_50))
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | sK6(sK10,sK7,sK9,sK8) != sK6(sK10,sK7,sK9,sK8)
    | sK10 != k11_lattice3(sK7,X0_50,X1_50) ),
    inference(instantiation,[status(thm)],[c_64225])).

cnf(c_66035,plain,
    ( ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),k11_lattice3(sK7,sK8,sK9))
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | sK6(sK10,sK7,sK9,sK8) != sK6(sK10,sK7,sK9,sK8)
    | sK10 != k11_lattice3(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_64398])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_38,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_38])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(k11_lattice3(sK7,X1,X0),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_5557,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | m1_subset_1(k11_lattice3(sK7,X1_50,X0_50),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_806])).

cnf(c_12441,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | m1_subset_1(k11_lattice3(sK7,X0_50,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5557])).

cnf(c_41041,plain,
    ( m1_subset_1(k11_lattice3(sK7,sK8,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_12441])).

cnf(c_5,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,k11_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5576,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | r1_orders_2(X0_49,X2_50,k11_lattice3(X0_49,X1_50,X0_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(k11_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7190,plain,
    ( ~ sP0(sK7,X0_50,X1_50)
    | ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),X0_50)
    | ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),X1_50)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),k11_lattice3(sK7,X1_50,X0_50))
    | ~ m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k11_lattice3(sK7,X1_50,X0_50),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5576])).

cnf(c_13099,plain,
    ( ~ sP0(sK7,sK9,X0_50)
    | ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),X0_50)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),k11_lattice3(sK7,X0_50,sK9))
    | ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9)
    | ~ m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k11_lattice3(sK7,X0_50,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7190])).

cnf(c_27602,plain,
    ( ~ sP0(sK7,sK9,sK8)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),k11_lattice3(sK7,sK8,sK9))
    | ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9)
    | ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8)
    | ~ m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k11_lattice3(sK7,sK8,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_13099])).

cnf(c_29,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | r2_yellow_0(X1,k2_tarski(X3,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1269,plain,
    ( r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | r2_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | sK10 != X4
    | sK9 != X3
    | sK8 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_32])).

cnf(c_1270,plain,
    ( r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1269])).

cnf(c_5551,plain,
    ( r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,X0_50,sK9)
    | ~ r1_orders_2(sK7,X0_50,sK8)
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1270])).

cnf(c_6287,plain,
    ( r1_orders_2(sK7,X0_50,sK10) = iProver_top
    | r1_orders_2(sK7,X0_50,sK9) != iProver_top
    | r1_orders_2(sK7,X0_50,sK8) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5551])).

cnf(c_25,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X0,X2)
    | ~ r1_orders_2(X1,X0,X3)
    | ~ r1_orders_2(X1,sK6(X0,X1,X2,X3),X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1446,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK6(X1,X0,X2,X3),X1)
    | r1_orders_2(sK7,X4,sK10)
    | ~ r1_orders_2(sK7,X4,sK9)
    | ~ r1_orders_2(sK7,X4,sK8)
    | ~ m1_subset_1(X4,u1_struct_0(sK7))
    | sK10 != X1
    | sK9 != X2
    | sK8 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_1447,plain,
    ( r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1446])).

cnf(c_5544,plain,
    ( r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,X0_50,sK9)
    | ~ r1_orders_2(sK7,X0_50,sK8)
    | ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1447])).

cnf(c_5586,plain,
    ( ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_5544])).

cnf(c_6297,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10) != iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5586])).

cnf(c_9537,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9) != iProver_top
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_6287,c_6297])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,sK10,sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1249,plain,
    ( r1_orders_2(sK7,sK10,sK8)
    | r2_yellow_0(X0,k2_tarski(X1,X2))
    | sK10 != X3
    | sK9 != X2
    | sK8 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_1250,plain,
    ( r1_orders_2(sK7,sK10,sK8)
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_1249])).

cnf(c_1251,plain,
    ( r1_orders_2(sK7,sK10,sK8) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_33,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | r1_orders_2(sK7,sK10,sK9) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1259,plain,
    ( r1_orders_2(sK7,sK10,sK9)
    | r2_yellow_0(X0,k2_tarski(X1,X2))
    | sK10 != X3
    | sK9 != X2
    | sK8 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_1260,plain,
    ( r1_orders_2(sK7,sK10,sK9)
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_1259])).

cnf(c_1261,plain,
    ( r1_orders_2(sK7,sK10,sK9) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_22,plain,
    ( r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_781,plain,
    ( r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_38])).

cnf(c_782,plain,
    ( r1_lattice3(sK7,k2_tarski(X0,X1),X2)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_5558,plain,
    ( r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50)
    | ~ r1_orders_2(sK7,X2_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_782])).

cnf(c_6450,plain,
    ( r1_lattice3(sK7,k2_tarski(X0_50,sK8),sK10)
    | ~ r1_orders_2(sK7,sK10,X0_50)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5558])).

cnf(c_6584,plain,
    ( r1_lattice3(sK7,k2_tarski(sK9,sK8),sK10)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_6450])).

cnf(c_6585,plain,
    ( r1_lattice3(sK7,k2_tarski(sK9,sK8),sK10) = iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6584])).

cnf(c_15,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_39,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_483,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_39])).

cnf(c_484,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_488,plain,
    ( m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0)
    | ~ r1_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_38])).

cnf(c_489,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_488])).

cnf(c_5567,plain,
    ( ~ r1_lattice3(sK7,X0_51,X0_50)
    | r2_yellow_0(sK7,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0_51,X0_50),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_489])).

cnf(c_6427,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50)
    | r2_yellow_0(sK7,k2_tarski(X0_50,X1_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,k2_tarski(X0_50,X1_50),X2_50),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5567])).

cnf(c_6832,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(sK9,sK8),sK10)
    | r2_yellow_0(sK7,k2_tarski(sK9,sK8))
    | m1_subset_1(sK4(sK7,k2_tarski(sK9,sK8),sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_6427])).

cnf(c_6839,plain,
    ( r1_lattice3(sK7,k2_tarski(sK9,sK8),sK10) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK9,sK8)) = iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(sK9,sK8),sK10),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6832])).

cnf(c_13,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_531,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_39])).

cnf(c_532,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | ~ r1_orders_2(sK7,sK4(sK7,X0,X1),X1)
    | r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0)
    | ~ r1_orders_2(sK7,sK4(sK7,X0,X1),X1)
    | ~ r1_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_38])).

cnf(c_537,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | ~ r1_orders_2(sK7,sK4(sK7,X0,X1),X1)
    | r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_536])).

cnf(c_5565,plain,
    ( ~ r1_lattice3(sK7,X0_51,X0_50)
    | ~ r1_orders_2(sK7,sK4(sK7,X0_51,X0_50),X0_50)
    | r2_yellow_0(sK7,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_537])).

cnf(c_6426,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50)
    | ~ r1_orders_2(sK7,sK4(sK7,k2_tarski(X0_50,X1_50),X2_50),X2_50)
    | r2_yellow_0(sK7,k2_tarski(X0_50,X1_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5565])).

cnf(c_6831,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(sK9,sK8),sK10)
    | ~ r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK10)
    | r2_yellow_0(sK7,k2_tarski(sK9,sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_6426])).

cnf(c_6841,plain,
    ( r1_lattice3(sK7,k2_tarski(sK9,sK8),sK10) != iProver_top
    | r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK10) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK9,sK8)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6831])).

cnf(c_14,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK4(X0,X1,X2))
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_507,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK4(X0,X1,X2))
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_39])).

cnf(c_508,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_lattice3(sK7,X0,sK4(sK7,X0,X1))
    | r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0)
    | r1_lattice3(sK7,X0,sK4(sK7,X0,X1))
    | ~ r1_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_38])).

cnf(c_513,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_lattice3(sK7,X0,sK4(sK7,X0,X1))
    | r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_512])).

cnf(c_5566,plain,
    ( ~ r1_lattice3(sK7,X0_51,X0_50)
    | r1_lattice3(sK7,X0_51,sK4(sK7,X0_51,X0_50))
    | r2_yellow_0(sK7,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_6425,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50)
    | r1_lattice3(sK7,k2_tarski(X0_50,X1_50),sK4(sK7,k2_tarski(X0_50,X1_50),X2_50))
    | r2_yellow_0(sK7,k2_tarski(X0_50,X1_50))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5566])).

cnf(c_6830,plain,
    ( r1_lattice3(sK7,k2_tarski(sK9,sK8),sK4(sK7,k2_tarski(sK9,sK8),sK10))
    | ~ r1_lattice3(sK7,k2_tarski(sK9,sK8),sK10)
    | r2_yellow_0(sK7,k2_tarski(sK9,sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_6425])).

cnf(c_6843,plain,
    ( r1_lattice3(sK7,k2_tarski(sK9,sK8),sK4(sK7,k2_tarski(sK9,sK8),sK10)) = iProver_top
    | r1_lattice3(sK7,k2_tarski(sK9,sK8),sK10) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK9,sK8)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6830])).

cnf(c_23,plain,
    ( ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_762,plain,
    ( ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_763,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(X0,X1),X2)
    | r1_orders_2(sK7,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_5559,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50)
    | r1_orders_2(sK7,X2_50,X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_763])).

cnf(c_7287,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(sK9,sK8),sK4(sK7,k2_tarski(sK9,sK8),sK10))
    | r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK8)
    | ~ m1_subset_1(sK4(sK7,k2_tarski(sK9,sK8),sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5559])).

cnf(c_7288,plain,
    ( r1_lattice3(sK7,k2_tarski(sK9,sK8),sK4(sK7,k2_tarski(sK9,sK8),sK10)) != iProver_top
    | r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK8) = iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(sK9,sK8),sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7287])).

cnf(c_24,plain,
    ( ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_741,plain,
    ( ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_742,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(X0,X1),X2)
    | r1_orders_2(sK7,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_5560,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50)
    | r1_orders_2(sK7,X2_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_742])).

cnf(c_7286,plain,
    ( ~ r1_lattice3(sK7,k2_tarski(sK9,sK8),sK4(sK7,k2_tarski(sK9,sK8),sK10))
    | r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK9)
    | ~ m1_subset_1(sK4(sK7,k2_tarski(sK9,sK8),sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5560])).

cnf(c_7290,plain,
    ( r1_lattice3(sK7,k2_tarski(sK9,sK8),sK4(sK7,k2_tarski(sK9,sK8),sK10)) != iProver_top
    | r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK9) = iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(sK9,sK8),sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7286])).

cnf(c_0,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5581,plain,
    ( k2_tarski(X0_50,X1_50) = k2_tarski(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_12190,plain,
    ( k2_tarski(sK8,sK9) = k2_tarski(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_5581])).

cnf(c_5596,plain,
    ( ~ r2_yellow_0(X0_49,X0_51)
    | r2_yellow_0(X0_49,X1_51)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_6391,plain,
    ( ~ r2_yellow_0(sK7,X0_51)
    | r2_yellow_0(sK7,X1_51)
    | X1_51 != X0_51 ),
    inference(instantiation,[status(thm)],[c_5596])).

cnf(c_9177,plain,
    ( r2_yellow_0(sK7,X0_51)
    | ~ r2_yellow_0(sK7,k2_tarski(sK9,sK8))
    | X0_51 != k2_tarski(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_6391])).

cnf(c_12266,plain,
    ( ~ r2_yellow_0(sK7,k2_tarski(sK9,sK8))
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k2_tarski(sK8,sK9) != k2_tarski(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_9177])).

cnf(c_12267,plain,
    ( k2_tarski(sK8,sK9) != k2_tarski(sK9,sK8)
    | r2_yellow_0(sK7,k2_tarski(sK9,sK8)) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12266])).

cnf(c_15313,plain,
    ( r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK10)
    | ~ r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK9)
    | ~ r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK8)
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | ~ m1_subset_1(sK4(sK7,k2_tarski(sK9,sK8),sK10),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5551])).

cnf(c_15314,plain,
    ( r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK10) = iProver_top
    | r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK9) != iProver_top
    | r1_orders_2(sK7,sK4(sK7,k2_tarski(sK9,sK8),sK10),sK8) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top
    | m1_subset_1(sK4(sK7,k2_tarski(sK9,sK8),sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15313])).

cnf(c_25459,plain,
    ( r2_yellow_0(sK7,k2_tarski(sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9537,c_42,c_43,c_44,c_1251,c_1261,c_6585,c_6839,c_6841,c_6843,c_7288,c_7290,c_12190,c_12267,c_15314])).

cnf(c_18,plain,
    ( ~ r2_yellow_0(X0,X1)
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_423,plain,
    ( ~ r2_yellow_0(X0,X1)
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_424,plain,
    ( ~ r2_yellow_0(sK7,X0)
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_428,plain,
    ( m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_38])).

cnf(c_429,plain,
    ( ~ r2_yellow_0(sK7,X0)
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_428])).

cnf(c_5570,plain,
    ( ~ r2_yellow_0(sK7,X0_51)
    | m1_subset_1(sK5(sK7,X0_51),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_6268,plain,
    ( r2_yellow_0(sK7,X0_51) != iProver_top
    | m1_subset_1(sK5(sK7,X0_51),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5570])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X2,X1,X3),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_555,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X2,X1,X3),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_39])).

cnf(c_556,plain,
    ( sP0(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | m1_subset_1(sK3(sK7,X1,X0,X2),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_560,plain,
    ( m1_subset_1(sK3(sK7,X1,X0,X2),u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ r1_orders_2(sK7,X2,X1)
    | sP0(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_38])).

cnf(c_561,plain,
    ( sP0(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK3(sK7,X1,X0,X2),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_560])).

cnf(c_5564,plain,
    ( sP0(sK7,X0_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7))
    | m1_subset_1(sK3(sK7,X1_50,X0_50,X2_50),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_561])).

cnf(c_6274,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,X2_50,X1_50) != iProver_top
    | r1_orders_2(sK7,X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X1_50,X0_50,X2_50),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5564])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,sK3(X0,X2,X1,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_588,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK3(X0,X2,X1,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_39])).

cnf(c_589,plain,
    ( sP0(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ r1_orders_2(sK7,X2,X1)
    | sP0(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_38])).

cnf(c_594,plain,
    ( sP0(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_593])).

cnf(c_5563,plain,
    ( sP0(sK7,X0_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X0_50)
    | r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,X2_50),X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_594])).

cnf(c_6275,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,X2_50,X1_50) != iProver_top
    | r1_orders_2(sK7,X2_50,X0_50) != iProver_top
    | r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,X2_50),X1_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5563])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,sK3(X0,X2,X1,X3),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_621,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK3(X0,X2,X1,X3),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_39])).

cnf(c_622,plain,
    ( sP0(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X0)
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ r1_orders_2(sK7,X2,X1)
    | sP0(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_38])).

cnf(c_625,plain,
    ( sP0(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_624])).

cnf(c_5562,plain,
    ( sP0(sK7,X0_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X0_50)
    | r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,X2_50),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_625])).

cnf(c_6276,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,X2_50,X1_50) != iProver_top
    | r1_orders_2(sK7,X2_50,X0_50) != iProver_top
    | r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,X2_50),X0_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5562])).

cnf(c_6280,plain,
    ( r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50) = iProver_top
    | r1_orders_2(sK7,X2_50,X1_50) != iProver_top
    | r1_orders_2(sK7,X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5558])).

cnf(c_16,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK5(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_459,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK5(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_39])).

cnf(c_460,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_orders_2(sK7,X1,sK5(sK7,X0))
    | ~ r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,X0)
    | r1_orders_2(sK7,X1,sK5(sK7,X0))
    | ~ r1_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_38])).

cnf(c_465,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_orders_2(sK7,X1,sK5(sK7,X0))
    | ~ r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_5568,plain,
    ( ~ r1_lattice3(sK7,X0_51,X0_50)
    | r1_orders_2(sK7,X0_50,sK5(sK7,X0_51))
    | ~ r2_yellow_0(sK7,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_6270,plain,
    ( r1_lattice3(sK7,X0_51,X0_50) != iProver_top
    | r1_orders_2(sK7,X0_50,sK5(sK7,X0_51)) = iProver_top
    | r2_yellow_0(sK7,X0_51) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5568])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,sK3(X0,X2,X1,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_650,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,sK3(X0,X2,X1,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_39])).

cnf(c_651,plain,
    ( sP0(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X2)
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ r1_orders_2(sK7,X2,X1)
    | sP0(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_38])).

cnf(c_656,plain,
    ( sP0(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X2,X1)
    | ~ r1_orders_2(sK7,X2,X0)
    | ~ r1_orders_2(sK7,sK3(sK7,X1,X0,X2),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_655])).

cnf(c_5561,plain,
    ( sP0(sK7,X0_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X1_50)
    | ~ r1_orders_2(sK7,X2_50,X0_50)
    | ~ r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,X2_50),X2_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_656])).

cnf(c_6277,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,X2_50,X1_50) != iProver_top
    | r1_orders_2(sK7,X2_50,X0_50) != iProver_top
    | r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,X2_50),X2_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5561])).

cnf(c_7901,plain,
    ( r1_lattice3(sK7,X0_51,sK3(sK7,X0_50,X1_50,sK5(sK7,X0_51))) != iProver_top
    | sP0(sK7,X1_50,X0_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,X0_51),X0_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X0_51),X1_50) != iProver_top
    | r2_yellow_0(sK7,X0_51) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X0_50,X1_50,sK5(sK7,X0_51)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X0_51),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6270,c_6277])).

cnf(c_5630,plain,
    ( r2_yellow_0(sK7,X0_51) != iProver_top
    | m1_subset_1(sK5(sK7,X0_51),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5570])).

cnf(c_14003,plain,
    ( m1_subset_1(sK3(sK7,X0_50,X1_50,sK5(sK7,X0_51)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0_51) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X0_51),X1_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X0_51),X0_50) != iProver_top
    | sP0(sK7,X1_50,X0_50) = iProver_top
    | r1_lattice3(sK7,X0_51,sK3(sK7,X0_50,X1_50,sK5(sK7,X0_51))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7901,c_5630])).

cnf(c_14004,plain,
    ( r1_lattice3(sK7,X0_51,sK3(sK7,X0_50,X1_50,sK5(sK7,X0_51))) != iProver_top
    | sP0(sK7,X1_50,X0_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,X0_51),X0_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,X0_51),X1_50) != iProver_top
    | r2_yellow_0(sK7,X0_51) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X0_50,X1_50,sK5(sK7,X0_51)),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14003])).

cnf(c_14009,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,sK5(sK7,k2_tarski(X2_50,X3_50))),X3_50) != iProver_top
    | r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,sK5(sK7,k2_tarski(X2_50,X3_50))),X2_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X2_50,X3_50)),X0_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X2_50,X3_50)),X1_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X2_50,X3_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X3_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X1_50,X0_50,sK5(sK7,k2_tarski(X2_50,X3_50))),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6280,c_14004])).

cnf(c_22627,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK3(sK7,X1_50,X0_50,sK5(sK7,k2_tarski(X2_50,X0_50))),X2_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X2_50,X0_50)),X1_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X2_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X2_50,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X1_50,X0_50,sK5(sK7,k2_tarski(X2_50,X0_50))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,k2_tarski(X2_50,X0_50)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6276,c_14009])).

cnf(c_23654,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X1_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X1_50,X0_50,sK5(sK7,k2_tarski(X1_50,X0_50))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,k2_tarski(X1_50,X0_50)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6275,c_22627])).

cnf(c_25447,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X1_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,k2_tarski(X1_50,X0_50)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6274,c_23654])).

cnf(c_25452,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X1_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_25447])).

cnf(c_17,plain,
    ( r1_lattice3(X0,X1,sK5(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_441,plain,
    ( r1_lattice3(X0,X1,sK5(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_442,plain,
    ( r1_lattice3(sK7,X0,sK5(sK7,X0))
    | ~ r2_yellow_0(sK7,X0)
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_446,plain,
    ( ~ r2_yellow_0(sK7,X0)
    | r1_lattice3(sK7,X0,sK5(sK7,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_38])).

cnf(c_447,plain,
    ( r1_lattice3(sK7,X0,sK5(sK7,X0))
    | ~ r2_yellow_0(sK7,X0) ),
    inference(renaming,[status(thm)],[c_446])).

cnf(c_5569,plain,
    ( r1_lattice3(sK7,X0_51,sK5(sK7,X0_51))
    | ~ r2_yellow_0(sK7,X0_51) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_6269,plain,
    ( r1_lattice3(sK7,X0_51,sK5(sK7,X0_51)) = iProver_top
    | r2_yellow_0(sK7,X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5569])).

cnf(c_6279,plain,
    ( r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_orders_2(sK7,X2_50,X1_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5559])).

cnf(c_7103,plain,
    ( r1_orders_2(sK7,sK5(sK7,k2_tarski(X0_50,X1_50)),X1_50) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(X0_50,X1_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,k2_tarski(X0_50,X1_50)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6269,c_6279])).

cnf(c_12339,plain,
    ( r1_orders_2(sK7,sK5(sK7,k2_tarski(X0_50,X1_50)),X1_50) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(X0_50,X1_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_7103])).

cnf(c_25453,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X1_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,k2_tarski(X0_50,X1_50)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5581,c_25447])).

cnf(c_25473,plain,
    ( m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X1_50) != iProver_top
    | sP0(sK7,X0_50,X1_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25453,c_25452])).

cnf(c_25474,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X1_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_25473])).

cnf(c_25483,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X0_50,X1_50)),X1_50) != iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5581,c_25474])).

cnf(c_6278,plain,
    ( r1_lattice3(sK7,k2_tarski(X0_50,X1_50),X2_50) != iProver_top
    | r1_orders_2(sK7,X2_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5560])).

cnf(c_6968,plain,
    ( r1_orders_2(sK7,sK5(sK7,k2_tarski(X0_50,X1_50)),X0_50) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(X0_50,X1_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,k2_tarski(X0_50,X1_50)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6269,c_6278])).

cnf(c_11998,plain,
    ( r1_orders_2(sK7,sK5(sK7,k2_tarski(X0_50,X1_50)),X0_50) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(X0_50,X1_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6268,c_6968])).

cnf(c_25479,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11998,c_25474])).

cnf(c_25518,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r1_orders_2(sK7,sK5(sK7,k2_tarski(X1_50,X0_50)),X0_50) != iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25483,c_25479])).

cnf(c_25526,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12339,c_25518])).

cnf(c_25624,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25452,c_25526])).

cnf(c_25625,plain,
    ( sP0(sK7,X0_50,X1_50) = iProver_top
    | r2_yellow_0(sK7,k2_tarski(X1_50,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_25624])).

cnf(c_25628,plain,
    ( sP0(sK7,sK9,sK8) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25459,c_25625])).

cnf(c_25633,plain,
    ( sP0(sK7,sK9,sK8)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25628])).

cnf(c_25461,plain,
    ( r2_yellow_0(sK7,k2_tarski(sK8,sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25459])).

cnf(c_30,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | k11_lattice3(X1,X3,X2) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1216,plain,
    ( r1_orders_2(sK7,sK10,sK9)
    | k11_lattice3(X0,X1,X2) = X3
    | sK10 != X3
    | sK9 != X2
    | sK8 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_33])).

cnf(c_1217,plain,
    ( r1_orders_2(sK7,sK10,sK9)
    | k11_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(unflattening,[status(thm)],[c_1216])).

cnf(c_5555,plain,
    ( r1_orders_2(sK7,sK10,sK9)
    | k11_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(subtyping,[status(esa)],[c_1217])).

cnf(c_6283,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK10,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5555])).

cnf(c_1226,plain,
    ( r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k11_lattice3(X1,X2,X3) = X4
    | sK10 != X4
    | sK9 != X3
    | sK8 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_1227,plain,
    ( r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k11_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(unflattening,[status(thm)],[c_1226])).

cnf(c_5554,plain,
    ( r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,X0_50,sK9)
    | ~ r1_orders_2(sK7,X0_50,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | k11_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(subtyping,[status(esa)],[c_1227])).

cnf(c_6284,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,X0_50,sK10) = iProver_top
    | r1_orders_2(sK7,X0_50,sK9) != iProver_top
    | r1_orders_2(sK7,X0_50,sK8) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5554])).

cnf(c_9269,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK10,sK10) = iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6283,c_6284])).

cnf(c_1206,plain,
    ( r1_orders_2(sK7,sK10,sK8)
    | k11_lattice3(X0,X1,X2) = X3
    | sK10 != X3
    | sK9 != X2
    | sK8 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_1207,plain,
    ( r1_orders_2(sK7,sK10,sK8)
    | k11_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(unflattening,[status(thm)],[c_1206])).

cnf(c_5556,plain,
    ( r1_orders_2(sK7,sK10,sK8)
    | k11_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(subtyping,[status(esa)],[c_1207])).

cnf(c_5668,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK10,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5556])).

cnf(c_5669,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK10,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5555])).

cnf(c_7416,plain,
    ( sP0(sK7,X0_50,sK8)
    | ~ r1_orders_2(sK7,sK10,X0_50)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | m1_subset_1(sK3(sK7,sK8,X0_50,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5564])).

cnf(c_7976,plain,
    ( sP0(sK7,sK9,sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | m1_subset_1(sK3(sK7,sK8,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7416])).

cnf(c_7977,plain,
    ( sP0(sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK3(sK7,sK8,sK9,sK10),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7976])).

cnf(c_7476,plain,
    ( sP0(sK7,X0_50,sK8)
    | ~ r1_orders_2(sK7,sK3(sK7,sK8,X0_50,sK10),sK10)
    | ~ r1_orders_2(sK7,sK10,X0_50)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5561])).

cnf(c_8090,plain,
    ( sP0(sK7,sK9,sK8)
    | ~ r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK10)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7476])).

cnf(c_8091,plain,
    ( sP0(sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK10) != iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8090])).

cnf(c_7576,plain,
    ( sP0(sK7,X0_50,sK8)
    | r1_orders_2(sK7,sK3(sK7,sK8,X0_50,sK10),sK8)
    | ~ r1_orders_2(sK7,sK10,X0_50)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5563])).

cnf(c_8235,plain,
    ( sP0(sK7,sK9,sK8)
    | r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7576])).

cnf(c_8236,plain,
    ( sP0(sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK8) = iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8235])).

cnf(c_7526,plain,
    ( sP0(sK7,X0_50,sK8)
    | r1_orders_2(sK7,sK3(sK7,sK8,X0_50,sK10),X0_50)
    | ~ r1_orders_2(sK7,sK10,X0_50)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5562])).

cnf(c_8349,plain,
    ( sP0(sK7,sK9,sK8)
    | r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK9)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7526])).

cnf(c_8350,plain,
    ( sP0(sK7,sK9,sK8) = iProver_top
    | r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK9) = iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8349])).

cnf(c_4,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0))
    | k11_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5577,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | m1_subset_1(sK2(X0_49,X0_50,X1_50,X2_50),u1_struct_0(X0_49))
    | k11_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_6261,plain,
    ( k11_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP0(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X0_50) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(sK2(X0_49,X1_50,X0_50,X2_50),u1_struct_0(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5577])).

cnf(c_3,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k11_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5578,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | r1_orders_2(X0_49,sK2(X0_49,X0_50,X1_50,X2_50),X1_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k11_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6260,plain,
    ( k11_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP0(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,sK2(X0_49,X1_50,X0_50,X2_50),X0_50) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5578])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k11_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5579,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | r1_orders_2(X0_49,sK2(X0_49,X0_50,X1_50,X2_50),X0_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k11_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_6259,plain,
    ( k11_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP0(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,sK2(X0_49,X1_50,X0_50,X2_50),X1_50) = iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5579])).

cnf(c_28,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X0,X2)
    | ~ r1_orders_2(X1,X0,X3)
    | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1296,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(sK7,X4,sK10)
    | ~ r1_orders_2(sK7,X4,sK9)
    | ~ r1_orders_2(sK7,X4,sK8)
    | ~ m1_subset_1(X4,u1_struct_0(sK7))
    | m1_subset_1(sK6(X1,X0,X2,X3),u1_struct_0(X0))
    | sK10 != X1
    | sK9 != X2
    | sK8 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_1297,plain,
    ( r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1296])).

cnf(c_5550,plain,
    ( r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,X0_50,sK9)
    | ~ r1_orders_2(sK7,X0_50,sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1297])).

cnf(c_5582,plain,
    ( r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,X0_50,sK9)
    | ~ r1_orders_2(sK7,X0_50,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_5550])).

cnf(c_6289,plain,
    ( r1_orders_2(sK7,X0_50,sK10) = iProver_top
    | r1_orders_2(sK7,X0_50,sK9) != iProver_top
    | r1_orders_2(sK7,X0_50,sK8) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5582])).

cnf(c_6959,plain,
    ( k11_lattice3(sK7,X0_50,sK9) = X1_50
    | sP0(sK7,sK9,X0_50) != iProver_top
    | r1_orders_2(sK7,X1_50,X0_50) != iProver_top
    | r1_orders_2(sK7,X1_50,sK9) != iProver_top
    | r1_orders_2(sK7,sK2(sK7,sK9,X0_50,X1_50),sK10) = iProver_top
    | r1_orders_2(sK7,sK2(sK7,sK9,X0_50,X1_50),sK8) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK2(sK7,sK9,X0_50,X1_50),u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6259,c_6289])).

cnf(c_9214,plain,
    ( k11_lattice3(sK7,sK8,sK9) = X0_50
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,X0_50,sK9) != iProver_top
    | r1_orders_2(sK7,X0_50,sK8) != iProver_top
    | r1_orders_2(sK7,sK2(sK7,sK9,sK8,X0_50),sK10) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK2(sK7,sK9,sK8,X0_50),u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6260,c_6959])).

cnf(c_10169,plain,
    ( k11_lattice3(sK7,sK8,sK9) = X0_50
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,X0_50,sK9) != iProver_top
    | r1_orders_2(sK7,X0_50,sK8) != iProver_top
    | r1_orders_2(sK7,sK2(sK7,sK9,sK8,X0_50),sK10) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6261,c_9214])).

cnf(c_1,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k11_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5580,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | ~ r1_orders_2(X0_49,sK2(X0_49,X0_50,X1_50,X2_50),X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k11_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6258,plain,
    ( k11_lattice3(X0_49,X0_50,X1_50) = X2_50
    | sP0(X0_49,X1_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,X2_50,X0_50) != iProver_top
    | r1_orders_2(X0_49,sK2(X0_49,X1_50,X0_50,X2_50),X2_50) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5580])).

cnf(c_12037,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_10169,c_6258])).

cnf(c_5583,plain,
    ( ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_5550])).

cnf(c_5678,plain,
    ( r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5583])).

cnf(c_27,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X0,X2)
    | ~ r1_orders_2(X1,X0,X3)
    | r1_orders_2(X1,sK6(X0,X1,X2,X3),X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1346,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X1,X0,X2,X3),X3)
    | r1_orders_2(sK7,X4,sK10)
    | ~ r1_orders_2(sK7,X4,sK9)
    | ~ r1_orders_2(sK7,X4,sK8)
    | ~ m1_subset_1(X4,u1_struct_0(sK7))
    | sK10 != X1
    | sK9 != X2
    | sK8 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_1347,plain,
    ( r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1346])).

cnf(c_5548,plain,
    ( r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,X0_50,sK9)
    | ~ r1_orders_2(sK7,X0_50,sK8)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1347])).

cnf(c_5584,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_5548])).

cnf(c_5683,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8) = iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5584])).

cnf(c_5689,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10) != iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5586])).

cnf(c_26,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X0,X2)
    | ~ r1_orders_2(X1,X0,X3)
    | r1_orders_2(X1,sK6(X0,X1,X2,X3),X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1396,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X1,X0,X2,X3),X2)
    | r1_orders_2(sK7,X4,sK10)
    | ~ r1_orders_2(sK7,X4,sK9)
    | ~ r1_orders_2(sK7,X4,sK8)
    | ~ m1_subset_1(X4,u1_struct_0(sK7))
    | sK10 != X1
    | sK9 != X2
    | sK8 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_1397,plain,
    ( r1_orders_2(sK7,X0,sK10)
    | ~ r1_orders_2(sK7,X0,sK9)
    | ~ r1_orders_2(sK7,X0,sK8)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1396])).

cnf(c_5546,plain,
    ( r1_orders_2(sK7,X0_50,sK10)
    | ~ r1_orders_2(sK7,X0_50,sK9)
    | ~ r1_orders_2(sK7,X0_50,sK8)
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1397])).

cnf(c_5585,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_5546])).

cnf(c_6294,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9) = iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5585])).

cnf(c_9270,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10) = iProver_top
    | r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK9) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) != iProver_top
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_6294,c_6284])).

cnf(c_12043,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | sP0(sK7,sK9,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12037,c_44,c_5668,c_5669,c_5678,c_5683,c_5689,c_9270])).

cnf(c_16153,plain,
    ( r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK10)
    | ~ r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK9)
    | ~ r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK8)
    | ~ m1_subset_1(sK3(sK7,sK8,sK9,sK10),u1_struct_0(sK7))
    | k11_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(instantiation,[status(thm)],[c_5554])).

cnf(c_16157,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10
    | r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK10) = iProver_top
    | r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK9) != iProver_top
    | r1_orders_2(sK7,sK3(sK7,sK8,sK9,sK10),sK8) != iProver_top
    | m1_subset_1(sK3(sK7,sK8,sK9,sK10),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16153])).

cnf(c_18824,plain,
    ( k11_lattice3(sK7,sK8,sK9) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9269,c_42,c_43,c_44,c_5668,c_5669,c_7977,c_8091,c_8236,c_8350,c_12043,c_16157])).

cnf(c_6281,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k11_lattice3(sK7,X1_50,X0_50),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5557])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1)
    | ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5575,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | r1_orders_2(X0_49,k11_lattice3(X0_49,X1_50,X0_50),X0_50)
    | ~ m1_subset_1(k11_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_6263,plain,
    ( sP0(X0_49,X0_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,k11_lattice3(X0_49,X1_50,X0_50),X0_50) = iProver_top
    | m1_subset_1(k11_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5575])).

cnf(c_6508,plain,
    ( sP0(sK7,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK7,k11_lattice3(sK7,X1_50,X0_50),X0_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6281,c_6263])).

cnf(c_18844,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18824,c_6508])).

cnf(c_18881,plain,
    ( ~ sP0(sK7,sK9,sK8)
    | r1_orders_2(sK7,sK10,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18844])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
    | ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5574,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | r1_orders_2(X0_49,k11_lattice3(X0_49,X1_50,X0_50),X1_50)
    | ~ m1_subset_1(k11_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_6264,plain,
    ( sP0(X0_49,X0_50,X1_50) != iProver_top
    | r1_orders_2(X0_49,k11_lattice3(X0_49,X1_50,X0_50),X1_50) = iProver_top
    | m1_subset_1(k11_lattice3(X0_49,X1_50,X0_50),u1_struct_0(X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5574])).

cnf(c_6597,plain,
    ( sP0(sK7,X0_50,X1_50) != iProver_top
    | r1_orders_2(sK7,k11_lattice3(sK7,X1_50,X0_50),X1_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6281,c_6264])).

cnf(c_18843,plain,
    ( sP0(sK7,sK9,sK8) != iProver_top
    | r1_orders_2(sK7,sK10,sK8) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18824,c_6597])).

cnf(c_18880,plain,
    ( ~ sP0(sK7,sK9,sK8)
    | r1_orders_2(sK7,sK10,sK8)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18843])).

cnf(c_5588,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_6544,plain,
    ( sK6(sK10,sK7,sK9,sK8) = sK6(sK10,sK7,sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_5588])).

cnf(c_31,negated_conjecture,
    ( sP1(sK10,sK7,sK9,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1473,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK6(X1,X0,X2,X3),X1)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10
    | sK10 != X1
    | sK9 != X2
    | sK8 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_1474,plain,
    ( ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(unflattening,[status(thm)],[c_1473])).

cnf(c_5543,plain,
    ( ~ r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK10)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(subtyping,[status(esa)],[c_1474])).

cnf(c_1423,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X1,X0,X2,X3),X2)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10
    | sK10 != X1
    | sK9 != X2
    | sK8 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_1424,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(unflattening,[status(thm)],[c_1423])).

cnf(c_5545,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK9)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(subtyping,[status(esa)],[c_1424])).

cnf(c_1373,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK6(X1,X0,X2,X3),X3)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10
    | sK10 != X1
    | sK9 != X2
    | sK8 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_1374,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(unflattening,[status(thm)],[c_1373])).

cnf(c_5547,plain,
    ( r1_orders_2(sK7,sK6(sK10,sK7,sK9,sK8),sK8)
    | ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(subtyping,[status(esa)],[c_1374])).

cnf(c_1323,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | m1_subset_1(sK6(X1,X0,X2,X3),u1_struct_0(X0))
    | k11_lattice3(sK7,sK8,sK9) != sK10
    | sK10 != X1
    | sK9 != X2
    | sK8 != X3
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_31])).

cnf(c_1324,plain,
    ( ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(unflattening,[status(thm)],[c_1323])).

cnf(c_5549,plain,
    ( ~ r1_orders_2(sK7,sK10,sK9)
    | ~ r1_orders_2(sK7,sK10,sK8)
    | ~ r2_yellow_0(sK7,k2_tarski(sK8,sK9))
    | m1_subset_1(sK6(sK10,sK7,sK9,sK8),u1_struct_0(sK7))
    | k11_lattice3(sK7,sK8,sK9) != sK10 ),
    inference(subtyping,[status(esa)],[c_1324])).

cnf(c_5607,plain,
    ( sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_5588])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_68770,c_66035,c_41041,c_27602,c_25633,c_25461,c_18881,c_18880,c_18824,c_6544,c_5543,c_5545,c_5547,c_5549,c_5607,c_36,c_37])).


%------------------------------------------------------------------------------

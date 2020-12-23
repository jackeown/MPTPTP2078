%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1542+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:50 EST 2020

% Result     : Theorem 7.40s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :  261 (4673 expanded)
%              Number of clauses        :  187 (1216 expanded)
%              Number of leaves         :   16 (1184 expanded)
%              Depth                    :   47
%              Number of atoms          : 1545 (37458 expanded)
%              Number of equality atoms :  334 (1752 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ sP2(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f29,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ sP2(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_yellow_0(X2,k2_tarski(X1,X0))
        & k10_lattice3(X2,X1,X0) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X2,X3,X4)
          & r1_orders_2(X2,X0,X4)
          & r1_orders_2(X2,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X2,X3,X4)
          & r1_orders_2(X2,X0,X4)
          & r1_orders_2(X2,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
        & r1_orders_2(X2,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_yellow_0(X2,k2_tarski(X1,X0))
        & k10_lattice3(X2,X1,X0) = X3 )
      | ( ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
        & r1_orders_2(X2,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,X1,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
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
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP2(X2,X1,X0,X3)
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f13,f19])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP2(X2,X1,X0,X3)
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v1_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(X0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_yellow_0(X0,k2_tarski(X1,sK10))
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_yellow_0(X0,k2_tarski(sK9,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v1_lattice3(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(sK8,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK8)) )
            & m1_subset_1(X1,u1_struct_0(sK8)) )
        | ~ v1_lattice3(sK8) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(sK8,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK8)) )
        | v1_lattice3(sK8) )
      & l1_orders_2(sK8)
      & v5_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
        & m1_subset_1(sK10,u1_struct_0(sK8))
        & m1_subset_1(sK9,u1_struct_0(sK8)) )
      | ~ v1_lattice3(sK8) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r1_yellow_0(sK8,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK8)) )
      | v1_lattice3(sK8) )
    & l1_orders_2(sK8)
    & v5_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f36,f39,f38,f37])).

fof(f68,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ r1_orders_2(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ r1_orders_2(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X2,k2_tarski(X1,X0))
      | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f16,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X3,X4)
                      | ~ r1_orders_2(X0,X2,X4)
                      | ~ r1_orders_2(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( r1_orders_2(X0,X7,X8)
                        | ~ r1_orders_2(X0,X6,X8)
                        | ~ r1_orders_2(X0,X5,X8)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f27,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X7,X8)
              | ~ r1_orders_2(X0,X6,X8)
              | ~ r1_orders_2(X0,X5,X8)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK6(X0,X5,X6))
        & r1_orders_2(X0,X5,sK6(X0,X5,X6))
        & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
        & r1_orders_2(X0,X2,sK5(X0,X3))
        & r1_orders_2(X0,X1,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r1_orders_2(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,sK4(X0),X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK4(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r1_orders_2(X0,sK3(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
                & r1_orders_2(X0,sK4(X0),sK5(X0,X3))
                & r1_orders_2(X0,sK3(X0),sK5(X0,X3))
                & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK4(X0),X3)
              | ~ r1_orders_2(X0,sK3(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK4(X0),u1_struct_0(X0))
          & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
                      | ~ r1_orders_2(X0,X6,X8)
                      | ~ r1_orders_2(X0,X5,X8)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X6,sK6(X0,X5,X6))
                  & r1_orders_2(X0,X5,sK6(X0,X5,X6))
                  & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f27,f26,f25,f24])).

fof(f49,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X4,X3] :
      ( r1_yellow_0(sK8,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK8))
      | ~ m1_subset_1(X3,u1_struct_0(sK8))
      | v1_lattice3(sK8) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X2,X4)
                            & r1_orders_2(X0,X1,X4) )
                         => r1_orders_2(X0,X3,X4) ) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f9,f17,f16])).

fof(f54,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X2,X1,X0) = X3
      | r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X2,X1,X0) = X3
      | ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f50,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | r1_orders_2(X0,sK3(X0),sK5(X0,X3))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | r1_orders_2(X0,sK4(X0),sK5(X0,X3))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | ~ r1_orders_2(X0,X3,sK5(X0,X3))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK6(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK6(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,
    ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f43,plain,(
    ! [X0] :
      ( v1_lattice3(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_orders_2(X2,X1,sK7(X0,X1,X2,X3))
    | r1_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,plain,
    ( sP2(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_475,plain,
    ( sP2(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_476,plain,
    ( sP2(X0,X1,sK8,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | sP2(X0,X1,sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_31])).

cnf(c_481,plain,
    ( sP2(X0,X1,sK8,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_831,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK7(X1,X3,X0,X2))
    | r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X2
    | X5 != X3
    | X6 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_481])).

cnf(c_832,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK7(X2,X0,sK8,X1))
    | r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_7101,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_orders_2(sK8,X0_49,sK7(X2_49,X0_49,sK8,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_832])).

cnf(c_7642,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,sK7(X2_49,X0_49,sK8,X1_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7101])).

cnf(c_16,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
    | r1_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_858,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK7(X1,X3,X0,X2))
    | r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X2
    | X5 != X3
    | X6 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_481])).

cnf(c_859,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK7(X2,X0,sK8,X1))
    | r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_7100,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_orders_2(sK8,X2_49,sK7(X2_49,X0_49,sK8,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_859])).

cnf(c_7643,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,sK7(X2_49,X0_49,sK8,X1_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7100])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X0,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X0,X2),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_439,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_440,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0,X2),X1)
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X2),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_444,plain,
    ( ~ m1_subset_1(k10_lattice3(sK8,X0,X2),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X2))
    | r1_orders_2(sK8,k10_lattice3(sK8,X0,X2),X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_31])).

cnf(c_445,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0,X2),X1)
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X2),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_571,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0,X2),X1)
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_546,c_445])).

cnf(c_7111,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X2_49),X1_49)
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_571])).

cnf(c_7632,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X2_49),X1_49) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7111])).

cnf(c_15,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
    | r1_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_883,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK7(X1,X3,X0,X2))
    | r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X2
    | X5 != X3
    | X6 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_481])).

cnf(c_884,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK7(X2,X0,sK8,X1))
    | r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_7099,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | ~ r1_orders_2(sK8,X1_49,sK7(X2_49,X0_49,sK8,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_884])).

cnf(c_7644,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X1_49,sK7(X2_49,X0_49,sK8,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7099])).

cnf(c_8737,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X3_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7632,c_7644])).

cnf(c_8982,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)))
    | ~ r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49))
    | ~ r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X3_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0_49,X3_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_7099,c_7111])).

cnf(c_7114,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_546])).

cnf(c_18,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_yellow_0(X2,k2_tarski(X1,X0))
    | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_804,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | m1_subset_1(sK7(X1,X3,X0,X2),u1_struct_0(X0))
    | X4 != X2
    | X5 != X3
    | X6 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_481])).

cnf(c_805,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2,X0,sK8,X1),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_7102,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2_49,X0_49,sK8,X1_49),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_805])).

cnf(c_9935,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)))
    | ~ r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49))
    | ~ r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X3_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8982,c_7114,c_7102])).

cnf(c_9936,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9935])).

cnf(c_14041,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8737,c_9936])).

cnf(c_14055,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X1_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7643,c_14041])).

cnf(c_7629,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7114])).

cnf(c_26,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_389,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_390,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X1))
    | r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_31])).

cnf(c_395,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_570,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_546,c_395])).

cnf(c_7112,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_570])).

cnf(c_7631,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7112])).

cnf(c_15905,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X1_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14055,c_7629,c_7631])).

cnf(c_15908,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7642,c_15905])).

cnf(c_7,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7120,plain,
    ( m1_subset_1(sK4(X0_48),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_7623,plain,
    ( m1_subset_1(sK4(X0_48),u1_struct_0(X0_48)) = iProver_top
    | sP0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7120])).

cnf(c_8,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7119,plain,
    ( m1_subset_1(sK3(X0_48),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_7624,plain,
    ( m1_subset_1(sK3(X0_48),u1_struct_0(X0_48)) = iProver_top
    | sP0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7119])).

cnf(c_30,negated_conjecture,
    ( r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | sP1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_353,plain,
    ( ~ l1_orders_2(X0)
    | sP0(X0)
    | ~ v1_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_13,c_2])).

cnf(c_535,plain,
    ( sP0(X0)
    | ~ v1_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_31])).

cnf(c_536,plain,
    ( sP0(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_2783,plain,
    ( sP0(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(prop_impl,[status(thm)],[c_536])).

cnf(c_2839,negated_conjecture,
    ( r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(bin_hyper_res,[status(thm)],[c_30,c_2783])).

cnf(c_7107,negated_conjecture,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(subtyping,[status(esa)],[c_2839])).

cnf(c_7636,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7107])).

cnf(c_0,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7125,plain,
    ( k2_tarski(X0_49,X1_49) = k2_tarski(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_20,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
    | k10_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_752,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK7(X1,X3,X0,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X2
    | X5 != X3
    | X6 != X1
    | k10_lattice3(X0,X3,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_481])).

cnf(c_753,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK7(X2,X0,sK8,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_7104,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_orders_2(sK8,X2_49,sK7(X2_49,X0_49,sK8,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_49,X2_49) = X1_49 ),
    inference(subtyping,[status(esa)],[c_753])).

cnf(c_7639,plain,
    ( k10_lattice3(sK8,X0_49,X1_49) = X2_49
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X1_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X1_49,sK7(X1_49,X0_49,sK8,X2_49)) = iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7104])).

cnf(c_19,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
    | k10_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_777,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK7(X1,X3,X0,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X2
    | X5 != X3
    | X6 != X1
    | k10_lattice3(X0,X3,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_481])).

cnf(c_778,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK7(X2,X0,sK8,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_7103,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | ~ r1_orders_2(sK8,X1_49,sK7(X2_49,X0_49,sK8,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_49,X2_49) = X1_49 ),
    inference(subtyping,[status(esa)],[c_778])).

cnf(c_7640,plain,
    ( k10_lattice3(sK8,X0_49,X1_49) = X2_49
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X1_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X2_49,sK7(X1_49,X0_49,sK8,X2_49)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7103])).

cnf(c_8842,plain,
    ( k10_lattice3(sK8,X0_49,X1_49) = X1_49
    | r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X1_49,X1_49) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7639,c_7640])).

cnf(c_9393,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X1_49),k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7631,c_8842])).

cnf(c_7167,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7114])).

cnf(c_9882,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X1_49),k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9393,c_7167])).

cnf(c_9883,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X1_49),k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9882])).

cnf(c_9893,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7632,c_9883])).

cnf(c_7173,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7112])).

cnf(c_10005,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9893,c_7167,c_7173])).

cnf(c_10006,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10005])).

cnf(c_25,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_416,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_417,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ r1_yellow_0(sK8,k2_tarski(X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_419,plain,
    ( ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_tarski(X1,X0))
    | r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_31])).

cnf(c_420,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ r1_yellow_0(sK8,k2_tarski(X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_569,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ r1_yellow_0(sK8,k2_tarski(X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_546,c_420])).

cnf(c_7113,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_7630,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7113])).

cnf(c_10016,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10006,c_7630])).

cnf(c_10021,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7125,c_10016])).

cnf(c_10286,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7636,c_10021])).

cnf(c_10510,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,sK3(sK8))) = k10_lattice3(sK8,X0_49,sK3(sK8))
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7624,c_10286])).

cnf(c_10651,plain,
    ( k10_lattice3(sK8,k10_lattice3(sK8,X0_49,X1_49),k10_lattice3(sK8,k10_lattice3(sK8,X0_49,X1_49),sK3(sK8))) = k10_lattice3(sK8,k10_lattice3(sK8,X0_49,X1_49),sK3(sK8))
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7629,c_10510])).

cnf(c_10886,plain,
    ( k10_lattice3(sK8,k10_lattice3(sK8,X0_49,sK4(sK8)),k10_lattice3(sK8,k10_lattice3(sK8,X0_49,sK4(sK8)),sK3(sK8))) = k10_lattice3(sK8,k10_lattice3(sK8,X0_49,sK4(sK8)),sK3(sK8))
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7623,c_10651])).

cnf(c_87,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_89,plain,
    ( m1_subset_1(sK3(sK8),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_90,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_92,plain,
    ( m1_subset_1(sK4(sK8),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_8009,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7114])).

cnf(c_8182,plain,
    ( m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8009])).

cnf(c_8183,plain,
    ( m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8182])).

cnf(c_8163,plain,
    ( r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,X0_49,sK4(sK8)))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,sK4(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7113])).

cnf(c_8667,plain,
    ( r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8163])).

cnf(c_8669,plain,
    ( r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8667])).

cnf(c_8148,plain,
    ( r1_yellow_0(sK8,k2_tarski(sK3(sK8),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7107])).

cnf(c_8668,plain,
    ( r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_8148])).

cnf(c_8671,plain,
    ( r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8))) = iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8668])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,sK3(X0),X1)
    | ~ r1_orders_2(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7121,plain,
    ( ~ r1_orders_2(X0_48,sK3(X0_48),X0_49)
    | ~ r1_orders_2(X0_48,sK4(X0_48),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | m1_subset_1(sK5(X0_48,X0_49),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_9178,plain,
    ( ~ r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7121])).

cnf(c_9179,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9178])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,sK3(X0),X1)
    | r1_orders_2(X0,sK3(X0),sK5(X0,X1))
    | ~ r1_orders_2(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7122,plain,
    ( ~ r1_orders_2(X0_48,sK3(X0_48),X0_49)
    | r1_orders_2(X0_48,sK3(X0_48),sK5(X0_48,X0_49))
    | ~ r1_orders_2(X0_48,sK4(X0_48),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_9177,plain,
    ( ~ r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | r1_orders_2(sK8,sK3(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7122])).

cnf(c_9181,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK3(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) = iProver_top
    | r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9177])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,sK3(X0),X1)
    | ~ r1_orders_2(X0,sK4(X0),X1)
    | r1_orders_2(X0,sK4(X0),sK5(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7123,plain,
    ( ~ r1_orders_2(X0_48,sK3(X0_48),X0_49)
    | ~ r1_orders_2(X0_48,sK4(X0_48),X0_49)
    | r1_orders_2(X0_48,sK4(X0_48),sK5(X0_48,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_9176,plain,
    ( ~ r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7123])).

cnf(c_9183,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) = iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9176])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,sK5(X0,X1))
    | ~ r1_orders_2(X0,sK3(X0),X1)
    | ~ r1_orders_2(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7124,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK5(X0_48,X0_49))
    | ~ r1_orders_2(X0_48,sK3(X0_48),X0_49)
    | ~ r1_orders_2(X0_48,sK4(X0_48),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_9175,plain,
    ( ~ r1_orders_2(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7124])).

cnf(c_9185,plain,
    ( r1_orders_2(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) != iProver_top
    | r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9175])).

cnf(c_8147,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),X0_49))
    | ~ r1_yellow_0(sK8,k2_tarski(sK3(sK8),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7112])).

cnf(c_9860,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8147])).

cnf(c_9861,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9860])).

cnf(c_12589,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,sK4(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7111])).

cnf(c_14406,plain,
    ( r1_orders_2(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK3(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_12589])).

cnf(c_14407,plain,
    ( r1_orders_2(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) = iProver_top
    | r1_orders_2(sK8,sK3(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14406])).

cnf(c_14424,plain,
    ( sP0(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10886,c_89,c_92,c_8183,c_8669,c_8671,c_9179,c_9181,c_9183,c_9185,c_9861,c_14407])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK6(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7118,plain,
    ( ~ r1_orders_2(X0_48,X0_49,X1_49)
    | ~ r1_orders_2(X0_48,X2_49,X1_49)
    | r1_orders_2(X0_48,sK6(X0_48,X2_49,X0_49),X1_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X2_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_15426,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_7118,c_7099])).

cnf(c_7625,plain,
    ( r1_orders_2(X0_48,X0_49,X1_49) != iProver_top
    | r1_orders_2(X0_48,X2_49,X1_49) != iProver_top
    | r1_orders_2(X0_48,sK6(X0_48,X2_49,X0_49),X1_49) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | sP0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7118])).

cnf(c_10052,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7625,c_7644])).

cnf(c_10181,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10052])).

cnf(c_14426,plain,
    ( sP0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14424])).

cnf(c_15470,plain,
    ( ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15426,c_10181,c_14426])).

cnf(c_15471,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_15470])).

cnf(c_15487,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15471,c_7102])).

cnf(c_15668,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X1_49,X0_49)))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X1_49,X0_49))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X1_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_15487,c_7100])).

cnf(c_15708,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK6(sK8,X0_49,X1_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_15668,c_7101])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7116,plain,
    ( r1_orders_2(X0_48,X0_49,sK6(X0_48,X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_8287,plain,
    ( r1_orders_2(sK8,X0_49,sK6(sK8,X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7116])).

cnf(c_16083,plain,
    ( ~ r1_orders_2(sK8,X1_49,sK6(sK8,X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15708,c_8287,c_14426])).

cnf(c_16084,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK6(sK8,X1_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_16083])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7117,plain,
    ( r1_orders_2(X0_48,X0_49,sK6(X0_48,X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_8361,plain,
    ( r1_orders_2(sK8,X0_49,sK6(sK8,X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7117])).

cnf(c_16087,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16084,c_8361,c_14426])).

cnf(c_16088,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_16087])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7115,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | m1_subset_1(sK6(X0_48,X1_49,X0_49),u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_16113,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_16088,c_7115])).

cnf(c_16114,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16113])).

cnf(c_16292,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15908,c_89,c_92,c_8183,c_8669,c_8671,c_9179,c_9181,c_9183,c_9185,c_9861,c_14407,c_16114])).

cnf(c_16293,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16292])).

cnf(c_27,negated_conjecture,
    ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_367,plain,
    ( ~ l1_orders_2(X0)
    | ~ sP0(X0)
    | v1_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_13,c_1])).

cnf(c_525,plain,
    ( ~ sP0(X0)
    | v1_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_367,c_31])).

cnf(c_526,plain,
    ( ~ sP0(sK8)
    | v1_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_2785,plain,
    ( ~ sP0(sK8)
    | v1_lattice3(sK8) ),
    inference(prop_impl,[status(thm)],[c_526])).

cnf(c_2836,negated_conjecture,
    ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ sP0(sK8) ),
    inference(bin_hyper_res,[status(thm)],[c_27,c_2785])).

cnf(c_7108,negated_conjecture,
    ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ sP0(sK8) ),
    inference(subtyping,[status(esa)],[c_2836])).

cnf(c_7635,plain,
    ( r1_yellow_0(sK8,k2_tarski(sK9,sK10)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7108])).

cnf(c_16303,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_16293,c_7635])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_590,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_526,c_28])).

cnf(c_591,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_581,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_526,c_29])).

cnf(c_582,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16303,c_14424,c_591,c_582])).


%------------------------------------------------------------------------------

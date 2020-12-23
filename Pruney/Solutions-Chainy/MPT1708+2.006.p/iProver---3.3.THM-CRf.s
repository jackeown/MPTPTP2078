%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:50 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 862 expanded)
%              Number of clauses        :   80 ( 177 expanded)
%              Number of leaves         :   20 ( 275 expanded)
%              Depth                    :   21
%              Number of atoms          :  903 (8645 expanded)
%              Number of equality atoms :  331 (1728 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f17,f30])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f64])).

fof(f32,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f33,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7
                & X5 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | X5 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X0 != X7
              & X1 != X7
              & X2 != X7
              & X3 != X7
              & X4 != X7
              & X5 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X0 = X7
            | X1 = X7
            | X2 = X7
            | X3 = X7
            | X4 = X7
            | X5 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X0 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X6,X4,X2,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X8,X1,X2,X3,X4,X5,X6) ) ),
    inference(equality_resolution,[],[f56])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X2)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
     => ( ( ! [X4] :
              ( sK5 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) )
          | ! [X5] :
              ( sK5 != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
        & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,sK4))) )
        & ~ r1_tsep_1(X1,sK4)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,sK3,X2))) )
            & ~ r1_tsep_1(sK3,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( X3 != X4
                          | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                      | ! [X5] :
                          ( X3 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                    & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ! [X4] :
          ( sK5 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
      | ! [X5] :
          ( sK5 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
    & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    & ~ r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f43,f42,f41,f40])).

fof(f81,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f87])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f88])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f89])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(X3)
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f70,f90])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f84,plain,(
    ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f90])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    ! [X4,X5] :
      ( sK5 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f103,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f102])).

fof(f85,plain,(
    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k4_enumset1(X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6118,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k4_enumset1(X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X0,X6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6126,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6) != iProver_top
    | r2_hidden(X0,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8435,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X2,X3,X4,X5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6118,c_6126])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_6107,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6114,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
    | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ l1_pre_topc(X2)
    | k1_setfam_1(k4_enumset1(u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1))) = u1_struct_0(k2_tsep_1(X2,X0,X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_29,negated_conjecture,
    ( ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_486,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ v1_pre_topc(k2_tsep_1(X1,X2,X0))
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | k1_setfam_1(k4_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0))) = u1_struct_0(k2_tsep_1(X1,X2,X0))
    | sK3 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_487,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_491,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
    | ~ l1_pre_topc(X0)
    | k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_33,c_31])).

cnf(c_6101,plain,
    ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
    | m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_9807,plain,
    ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6114,c_6101])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_42,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6610,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_6963,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK4,X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6610])).

cnf(c_6964,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6963])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6611,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK3,X1)
    | v1_pre_topc(k2_tsep_1(X1,sK3,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_6971,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK4,X0)
    | v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6611])).

cnf(c_6972,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6971])).

cnf(c_10285,plain,
    ( v2_struct_0(X0) = iProver_top
    | k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9807,c_40,c_42,c_6964,c_6972])).

cnf(c_10286,plain,
    ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10285])).

cnf(c_10296,plain,
    ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6107,c_10286])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_494,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_6495,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v1_pre_topc(k2_tsep_1(sK2,sK3,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_6649,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6495])).

cnf(c_6509,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK2,sK3,X0))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_6670,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6509])).

cnf(c_6519,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_pre_topc(k2_tsep_1(sK2,sK3,X0),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_6790,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6519])).

cnf(c_10861,plain,
    ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10296,c_36,c_34,c_33,c_32,c_31,c_30,c_494,c_6649,c_6670,c_6790])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6117,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10918,plain,
    ( r2_hidden(X0,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top
    | r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10861,c_6117])).

cnf(c_11099,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8435,c_10918])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_387,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_388,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_390,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_34])).

cnf(c_391,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_6103,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_11580,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11099,c_6103])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6134,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10917,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10861,c_6134])).

cnf(c_10931,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10917,c_6103])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9780,plain,
    ( m1_subset_1(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_10827,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    | m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_9780])).

cnf(c_10830,plain,
    ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10827])).

cnf(c_10821,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    | m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_9780])).

cnf(c_10822,plain,
    ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10821])).

cnf(c_6791,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6790])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6116,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6765,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6107,c_6116])).

cnf(c_6109,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6764,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6109,c_6116])).

cnf(c_6671,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6670])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_43,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_39,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11580,c_10931,c_10830,c_10822,c_6791,c_6765,c_6764,c_6671,c_46,c_45,c_43,c_42,c_41,c_40,c_39,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.05/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/0.99  
% 3.05/0.99  ------  iProver source info
% 3.05/0.99  
% 3.05/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.05/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/0.99  git: non_committed_changes: false
% 3.05/0.99  git: last_make_outside_of_git: false
% 3.05/0.99  
% 3.05/0.99  ------ 
% 3.05/0.99  
% 3.05/0.99  ------ Input Options
% 3.05/0.99  
% 3.05/0.99  --out_options                           all
% 3.05/0.99  --tptp_safe_out                         true
% 3.05/0.99  --problem_path                          ""
% 3.05/0.99  --include_path                          ""
% 3.05/0.99  --clausifier                            res/vclausify_rel
% 3.05/0.99  --clausifier_options                    --mode clausify
% 3.05/0.99  --stdin                                 false
% 3.05/0.99  --stats_out                             all
% 3.05/0.99  
% 3.05/0.99  ------ General Options
% 3.05/0.99  
% 3.05/0.99  --fof                                   false
% 3.05/0.99  --time_out_real                         305.
% 3.05/0.99  --time_out_virtual                      -1.
% 3.05/0.99  --symbol_type_check                     false
% 3.05/0.99  --clausify_out                          false
% 3.05/0.99  --sig_cnt_out                           false
% 3.05/0.99  --trig_cnt_out                          false
% 3.05/0.99  --trig_cnt_out_tolerance                1.
% 3.05/0.99  --trig_cnt_out_sk_spl                   false
% 3.05/0.99  --abstr_cl_out                          false
% 3.05/0.99  
% 3.05/0.99  ------ Global Options
% 3.05/0.99  
% 3.05/0.99  --schedule                              default
% 3.05/0.99  --add_important_lit                     false
% 3.05/0.99  --prop_solver_per_cl                    1000
% 3.05/0.99  --min_unsat_core                        false
% 3.05/0.99  --soft_assumptions                      false
% 3.05/0.99  --soft_lemma_size                       3
% 3.05/0.99  --prop_impl_unit_size                   0
% 3.05/0.99  --prop_impl_unit                        []
% 3.05/0.99  --share_sel_clauses                     true
% 3.05/0.99  --reset_solvers                         false
% 3.05/0.99  --bc_imp_inh                            [conj_cone]
% 3.05/0.99  --conj_cone_tolerance                   3.
% 3.05/0.99  --extra_neg_conj                        none
% 3.05/0.99  --large_theory_mode                     true
% 3.05/0.99  --prolific_symb_bound                   200
% 3.05/0.99  --lt_threshold                          2000
% 3.05/0.99  --clause_weak_htbl                      true
% 3.05/0.99  --gc_record_bc_elim                     false
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing Options
% 3.05/0.99  
% 3.05/0.99  --preprocessing_flag                    true
% 3.05/0.99  --time_out_prep_mult                    0.1
% 3.05/0.99  --splitting_mode                        input
% 3.05/0.99  --splitting_grd                         true
% 3.05/0.99  --splitting_cvd                         false
% 3.05/0.99  --splitting_cvd_svl                     false
% 3.05/0.99  --splitting_nvd                         32
% 3.05/0.99  --sub_typing                            true
% 3.05/0.99  --prep_gs_sim                           true
% 3.05/0.99  --prep_unflatten                        true
% 3.05/0.99  --prep_res_sim                          true
% 3.05/0.99  --prep_upred                            true
% 3.05/0.99  --prep_sem_filter                       exhaustive
% 3.05/0.99  --prep_sem_filter_out                   false
% 3.05/0.99  --pred_elim                             true
% 3.05/0.99  --res_sim_input                         true
% 3.05/0.99  --eq_ax_congr_red                       true
% 3.05/0.99  --pure_diseq_elim                       true
% 3.05/0.99  --brand_transform                       false
% 3.05/0.99  --non_eq_to_eq                          false
% 3.05/0.99  --prep_def_merge                        true
% 3.05/0.99  --prep_def_merge_prop_impl              false
% 3.05/0.99  --prep_def_merge_mbd                    true
% 3.05/0.99  --prep_def_merge_tr_red                 false
% 3.05/0.99  --prep_def_merge_tr_cl                  false
% 3.05/0.99  --smt_preprocessing                     true
% 3.05/0.99  --smt_ac_axioms                         fast
% 3.05/0.99  --preprocessed_out                      false
% 3.05/0.99  --preprocessed_stats                    false
% 3.05/0.99  
% 3.05/0.99  ------ Abstraction refinement Options
% 3.05/0.99  
% 3.05/0.99  --abstr_ref                             []
% 3.05/0.99  --abstr_ref_prep                        false
% 3.05/0.99  --abstr_ref_until_sat                   false
% 3.05/0.99  --abstr_ref_sig_restrict                funpre
% 3.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.99  --abstr_ref_under                       []
% 3.05/0.99  
% 3.05/0.99  ------ SAT Options
% 3.05/0.99  
% 3.05/0.99  --sat_mode                              false
% 3.05/0.99  --sat_fm_restart_options                ""
% 3.05/0.99  --sat_gr_def                            false
% 3.05/0.99  --sat_epr_types                         true
% 3.05/0.99  --sat_non_cyclic_types                  false
% 3.05/0.99  --sat_finite_models                     false
% 3.05/0.99  --sat_fm_lemmas                         false
% 3.05/0.99  --sat_fm_prep                           false
% 3.05/0.99  --sat_fm_uc_incr                        true
% 3.05/0.99  --sat_out_model                         small
% 3.05/0.99  --sat_out_clauses                       false
% 3.05/0.99  
% 3.05/0.99  ------ QBF Options
% 3.05/0.99  
% 3.05/0.99  --qbf_mode                              false
% 3.05/0.99  --qbf_elim_univ                         false
% 3.05/0.99  --qbf_dom_inst                          none
% 3.05/0.99  --qbf_dom_pre_inst                      false
% 3.05/0.99  --qbf_sk_in                             false
% 3.05/0.99  --qbf_pred_elim                         true
% 3.05/0.99  --qbf_split                             512
% 3.05/0.99  
% 3.05/0.99  ------ BMC1 Options
% 3.05/0.99  
% 3.05/0.99  --bmc1_incremental                      false
% 3.05/0.99  --bmc1_axioms                           reachable_all
% 3.05/0.99  --bmc1_min_bound                        0
% 3.05/0.99  --bmc1_max_bound                        -1
% 3.05/0.99  --bmc1_max_bound_default                -1
% 3.05/0.99  --bmc1_symbol_reachability              true
% 3.05/0.99  --bmc1_property_lemmas                  false
% 3.05/0.99  --bmc1_k_induction                      false
% 3.05/0.99  --bmc1_non_equiv_states                 false
% 3.05/0.99  --bmc1_deadlock                         false
% 3.05/0.99  --bmc1_ucm                              false
% 3.05/0.99  --bmc1_add_unsat_core                   none
% 3.05/0.99  --bmc1_unsat_core_children              false
% 3.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.99  --bmc1_out_stat                         full
% 3.05/0.99  --bmc1_ground_init                      false
% 3.05/0.99  --bmc1_pre_inst_next_state              false
% 3.05/0.99  --bmc1_pre_inst_state                   false
% 3.05/0.99  --bmc1_pre_inst_reach_state             false
% 3.05/0.99  --bmc1_out_unsat_core                   false
% 3.05/0.99  --bmc1_aig_witness_out                  false
% 3.05/0.99  --bmc1_verbose                          false
% 3.05/0.99  --bmc1_dump_clauses_tptp                false
% 3.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.99  --bmc1_dump_file                        -
% 3.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.99  --bmc1_ucm_extend_mode                  1
% 3.05/0.99  --bmc1_ucm_init_mode                    2
% 3.05/0.99  --bmc1_ucm_cone_mode                    none
% 3.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.99  --bmc1_ucm_relax_model                  4
% 3.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.99  --bmc1_ucm_layered_model                none
% 3.05/0.99  --bmc1_ucm_max_lemma_size               10
% 3.05/0.99  
% 3.05/0.99  ------ AIG Options
% 3.05/0.99  
% 3.05/0.99  --aig_mode                              false
% 3.05/0.99  
% 3.05/0.99  ------ Instantiation Options
% 3.05/0.99  
% 3.05/0.99  --instantiation_flag                    true
% 3.05/0.99  --inst_sos_flag                         false
% 3.05/0.99  --inst_sos_phase                        true
% 3.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel_side                     num_symb
% 3.05/0.99  --inst_solver_per_active                1400
% 3.05/0.99  --inst_solver_calls_frac                1.
% 3.05/0.99  --inst_passive_queue_type               priority_queues
% 3.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.99  --inst_passive_queues_freq              [25;2]
% 3.05/0.99  --inst_dismatching                      true
% 3.05/0.99  --inst_eager_unprocessed_to_passive     true
% 3.05/0.99  --inst_prop_sim_given                   true
% 3.05/0.99  --inst_prop_sim_new                     false
% 3.05/0.99  --inst_subs_new                         false
% 3.05/0.99  --inst_eq_res_simp                      false
% 3.05/0.99  --inst_subs_given                       false
% 3.05/0.99  --inst_orphan_elimination               true
% 3.05/0.99  --inst_learning_loop_flag               true
% 3.05/0.99  --inst_learning_start                   3000
% 3.05/0.99  --inst_learning_factor                  2
% 3.05/0.99  --inst_start_prop_sim_after_learn       3
% 3.05/0.99  --inst_sel_renew                        solver
% 3.05/0.99  --inst_lit_activity_flag                true
% 3.05/0.99  --inst_restr_to_given                   false
% 3.05/0.99  --inst_activity_threshold               500
% 3.05/0.99  --inst_out_proof                        true
% 3.05/0.99  
% 3.05/0.99  ------ Resolution Options
% 3.05/0.99  
% 3.05/0.99  --resolution_flag                       true
% 3.05/0.99  --res_lit_sel                           adaptive
% 3.05/0.99  --res_lit_sel_side                      none
% 3.05/0.99  --res_ordering                          kbo
% 3.05/0.99  --res_to_prop_solver                    active
% 3.05/0.99  --res_prop_simpl_new                    false
% 3.05/0.99  --res_prop_simpl_given                  true
% 3.05/0.99  --res_passive_queue_type                priority_queues
% 3.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.99  --res_passive_queues_freq               [15;5]
% 3.05/0.99  --res_forward_subs                      full
% 3.05/0.99  --res_backward_subs                     full
% 3.05/0.99  --res_forward_subs_resolution           true
% 3.05/0.99  --res_backward_subs_resolution          true
% 3.05/0.99  --res_orphan_elimination                true
% 3.05/0.99  --res_time_limit                        2.
% 3.05/0.99  --res_out_proof                         true
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Options
% 3.05/0.99  
% 3.05/0.99  --superposition_flag                    true
% 3.05/0.99  --sup_passive_queue_type                priority_queues
% 3.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.99  --demod_completeness_check              fast
% 3.05/0.99  --demod_use_ground                      true
% 3.05/0.99  --sup_to_prop_solver                    passive
% 3.05/0.99  --sup_prop_simpl_new                    true
% 3.05/0.99  --sup_prop_simpl_given                  true
% 3.05/0.99  --sup_fun_splitting                     false
% 3.05/0.99  --sup_smt_interval                      50000
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Simplification Setup
% 3.05/0.99  
% 3.05/0.99  --sup_indices_passive                   []
% 3.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_full_bw                           [BwDemod]
% 3.05/0.99  --sup_immed_triv                        [TrivRules]
% 3.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_immed_bw_main                     []
% 3.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  
% 3.05/0.99  ------ Combination Options
% 3.05/0.99  
% 3.05/0.99  --comb_res_mult                         3
% 3.05/0.99  --comb_sup_mult                         2
% 3.05/0.99  --comb_inst_mult                        10
% 3.05/0.99  
% 3.05/0.99  ------ Debug Options
% 3.05/0.99  
% 3.05/0.99  --dbg_backtrace                         false
% 3.05/0.99  --dbg_dump_prop_clauses                 false
% 3.05/0.99  --dbg_dump_prop_clauses_file            -
% 3.05/0.99  --dbg_out_stat                          false
% 3.05/0.99  ------ Parsing...
% 3.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/0.99  ------ Proving...
% 3.05/0.99  ------ Problem Properties 
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  clauses                                 35
% 3.05/0.99  conjectures                             8
% 3.05/0.99  EPR                                     14
% 3.05/0.99  Horn                                    27
% 3.05/0.99  unary                                   9
% 3.05/0.99  binary                                  9
% 3.05/0.99  lits                                    116
% 3.05/0.99  lits eq                                 22
% 3.05/0.99  fd_pure                                 0
% 3.05/0.99  fd_pseudo                               0
% 3.05/0.99  fd_cond                                 0
% 3.05/0.99  fd_pseudo_cond                          3
% 3.05/0.99  AC symbols                              0
% 3.05/0.99  
% 3.05/0.99  ------ Schedule dynamic 5 is on 
% 3.05/0.99  
% 3.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  ------ 
% 3.05/0.99  Current options:
% 3.05/0.99  ------ 
% 3.05/0.99  
% 3.05/0.99  ------ Input Options
% 3.05/0.99  
% 3.05/0.99  --out_options                           all
% 3.05/0.99  --tptp_safe_out                         true
% 3.05/0.99  --problem_path                          ""
% 3.05/0.99  --include_path                          ""
% 3.05/0.99  --clausifier                            res/vclausify_rel
% 3.05/0.99  --clausifier_options                    --mode clausify
% 3.05/0.99  --stdin                                 false
% 3.05/0.99  --stats_out                             all
% 3.05/0.99  
% 3.05/0.99  ------ General Options
% 3.05/0.99  
% 3.05/0.99  --fof                                   false
% 3.05/0.99  --time_out_real                         305.
% 3.05/0.99  --time_out_virtual                      -1.
% 3.05/0.99  --symbol_type_check                     false
% 3.05/0.99  --clausify_out                          false
% 3.05/0.99  --sig_cnt_out                           false
% 3.05/0.99  --trig_cnt_out                          false
% 3.05/0.99  --trig_cnt_out_tolerance                1.
% 3.05/0.99  --trig_cnt_out_sk_spl                   false
% 3.05/0.99  --abstr_cl_out                          false
% 3.05/0.99  
% 3.05/0.99  ------ Global Options
% 3.05/0.99  
% 3.05/0.99  --schedule                              default
% 3.05/0.99  --add_important_lit                     false
% 3.05/0.99  --prop_solver_per_cl                    1000
% 3.05/0.99  --min_unsat_core                        false
% 3.05/0.99  --soft_assumptions                      false
% 3.05/0.99  --soft_lemma_size                       3
% 3.05/0.99  --prop_impl_unit_size                   0
% 3.05/0.99  --prop_impl_unit                        []
% 3.05/0.99  --share_sel_clauses                     true
% 3.05/0.99  --reset_solvers                         false
% 3.05/0.99  --bc_imp_inh                            [conj_cone]
% 3.05/0.99  --conj_cone_tolerance                   3.
% 3.05/0.99  --extra_neg_conj                        none
% 3.05/0.99  --large_theory_mode                     true
% 3.05/0.99  --prolific_symb_bound                   200
% 3.05/0.99  --lt_threshold                          2000
% 3.05/0.99  --clause_weak_htbl                      true
% 3.05/0.99  --gc_record_bc_elim                     false
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing Options
% 3.05/0.99  
% 3.05/0.99  --preprocessing_flag                    true
% 3.05/0.99  --time_out_prep_mult                    0.1
% 3.05/0.99  --splitting_mode                        input
% 3.05/0.99  --splitting_grd                         true
% 3.05/0.99  --splitting_cvd                         false
% 3.05/0.99  --splitting_cvd_svl                     false
% 3.05/0.99  --splitting_nvd                         32
% 3.05/0.99  --sub_typing                            true
% 3.05/0.99  --prep_gs_sim                           true
% 3.05/0.99  --prep_unflatten                        true
% 3.05/0.99  --prep_res_sim                          true
% 3.05/0.99  --prep_upred                            true
% 3.05/0.99  --prep_sem_filter                       exhaustive
% 3.05/0.99  --prep_sem_filter_out                   false
% 3.05/0.99  --pred_elim                             true
% 3.05/0.99  --res_sim_input                         true
% 3.05/0.99  --eq_ax_congr_red                       true
% 3.05/0.99  --pure_diseq_elim                       true
% 3.05/0.99  --brand_transform                       false
% 3.05/0.99  --non_eq_to_eq                          false
% 3.05/0.99  --prep_def_merge                        true
% 3.05/0.99  --prep_def_merge_prop_impl              false
% 3.05/0.99  --prep_def_merge_mbd                    true
% 3.05/0.99  --prep_def_merge_tr_red                 false
% 3.05/0.99  --prep_def_merge_tr_cl                  false
% 3.05/0.99  --smt_preprocessing                     true
% 3.05/0.99  --smt_ac_axioms                         fast
% 3.05/0.99  --preprocessed_out                      false
% 3.05/0.99  --preprocessed_stats                    false
% 3.05/0.99  
% 3.05/0.99  ------ Abstraction refinement Options
% 3.05/0.99  
% 3.05/0.99  --abstr_ref                             []
% 3.05/0.99  --abstr_ref_prep                        false
% 3.05/0.99  --abstr_ref_until_sat                   false
% 3.05/0.99  --abstr_ref_sig_restrict                funpre
% 3.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.99  --abstr_ref_under                       []
% 3.05/0.99  
% 3.05/0.99  ------ SAT Options
% 3.05/0.99  
% 3.05/0.99  --sat_mode                              false
% 3.05/0.99  --sat_fm_restart_options                ""
% 3.05/0.99  --sat_gr_def                            false
% 3.05/0.99  --sat_epr_types                         true
% 3.05/0.99  --sat_non_cyclic_types                  false
% 3.05/0.99  --sat_finite_models                     false
% 3.05/0.99  --sat_fm_lemmas                         false
% 3.05/0.99  --sat_fm_prep                           false
% 3.05/0.99  --sat_fm_uc_incr                        true
% 3.05/0.99  --sat_out_model                         small
% 3.05/0.99  --sat_out_clauses                       false
% 3.05/0.99  
% 3.05/0.99  ------ QBF Options
% 3.05/0.99  
% 3.05/0.99  --qbf_mode                              false
% 3.05/0.99  --qbf_elim_univ                         false
% 3.05/0.99  --qbf_dom_inst                          none
% 3.05/0.99  --qbf_dom_pre_inst                      false
% 3.05/0.99  --qbf_sk_in                             false
% 3.05/0.99  --qbf_pred_elim                         true
% 3.05/0.99  --qbf_split                             512
% 3.05/0.99  
% 3.05/0.99  ------ BMC1 Options
% 3.05/0.99  
% 3.05/0.99  --bmc1_incremental                      false
% 3.05/0.99  --bmc1_axioms                           reachable_all
% 3.05/0.99  --bmc1_min_bound                        0
% 3.05/0.99  --bmc1_max_bound                        -1
% 3.05/0.99  --bmc1_max_bound_default                -1
% 3.05/0.99  --bmc1_symbol_reachability              true
% 3.05/0.99  --bmc1_property_lemmas                  false
% 3.05/0.99  --bmc1_k_induction                      false
% 3.05/0.99  --bmc1_non_equiv_states                 false
% 3.05/0.99  --bmc1_deadlock                         false
% 3.05/0.99  --bmc1_ucm                              false
% 3.05/0.99  --bmc1_add_unsat_core                   none
% 3.05/0.99  --bmc1_unsat_core_children              false
% 3.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.99  --bmc1_out_stat                         full
% 3.05/0.99  --bmc1_ground_init                      false
% 3.05/0.99  --bmc1_pre_inst_next_state              false
% 3.05/0.99  --bmc1_pre_inst_state                   false
% 3.05/0.99  --bmc1_pre_inst_reach_state             false
% 3.05/0.99  --bmc1_out_unsat_core                   false
% 3.05/0.99  --bmc1_aig_witness_out                  false
% 3.05/0.99  --bmc1_verbose                          false
% 3.05/0.99  --bmc1_dump_clauses_tptp                false
% 3.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.99  --bmc1_dump_file                        -
% 3.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.99  --bmc1_ucm_extend_mode                  1
% 3.05/0.99  --bmc1_ucm_init_mode                    2
% 3.05/0.99  --bmc1_ucm_cone_mode                    none
% 3.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.99  --bmc1_ucm_relax_model                  4
% 3.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.99  --bmc1_ucm_layered_model                none
% 3.05/0.99  --bmc1_ucm_max_lemma_size               10
% 3.05/0.99  
% 3.05/0.99  ------ AIG Options
% 3.05/0.99  
% 3.05/0.99  --aig_mode                              false
% 3.05/0.99  
% 3.05/0.99  ------ Instantiation Options
% 3.05/0.99  
% 3.05/0.99  --instantiation_flag                    true
% 3.05/0.99  --inst_sos_flag                         false
% 3.05/0.99  --inst_sos_phase                        true
% 3.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel_side                     none
% 3.05/0.99  --inst_solver_per_active                1400
% 3.05/0.99  --inst_solver_calls_frac                1.
% 3.05/0.99  --inst_passive_queue_type               priority_queues
% 3.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.99  --inst_passive_queues_freq              [25;2]
% 3.05/0.99  --inst_dismatching                      true
% 3.05/0.99  --inst_eager_unprocessed_to_passive     true
% 3.05/0.99  --inst_prop_sim_given                   true
% 3.05/0.99  --inst_prop_sim_new                     false
% 3.05/0.99  --inst_subs_new                         false
% 3.05/0.99  --inst_eq_res_simp                      false
% 3.05/0.99  --inst_subs_given                       false
% 3.05/0.99  --inst_orphan_elimination               true
% 3.05/0.99  --inst_learning_loop_flag               true
% 3.05/0.99  --inst_learning_start                   3000
% 3.05/0.99  --inst_learning_factor                  2
% 3.05/0.99  --inst_start_prop_sim_after_learn       3
% 3.05/0.99  --inst_sel_renew                        solver
% 3.05/0.99  --inst_lit_activity_flag                true
% 3.05/0.99  --inst_restr_to_given                   false
% 3.05/0.99  --inst_activity_threshold               500
% 3.05/0.99  --inst_out_proof                        true
% 3.05/0.99  
% 3.05/0.99  ------ Resolution Options
% 3.05/0.99  
% 3.05/0.99  --resolution_flag                       false
% 3.05/0.99  --res_lit_sel                           adaptive
% 3.05/0.99  --res_lit_sel_side                      none
% 3.05/0.99  --res_ordering                          kbo
% 3.05/0.99  --res_to_prop_solver                    active
% 3.05/0.99  --res_prop_simpl_new                    false
% 3.05/0.99  --res_prop_simpl_given                  true
% 3.05/0.99  --res_passive_queue_type                priority_queues
% 3.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.99  --res_passive_queues_freq               [15;5]
% 3.05/0.99  --res_forward_subs                      full
% 3.05/0.99  --res_backward_subs                     full
% 3.05/0.99  --res_forward_subs_resolution           true
% 3.05/0.99  --res_backward_subs_resolution          true
% 3.05/0.99  --res_orphan_elimination                true
% 3.05/0.99  --res_time_limit                        2.
% 3.05/0.99  --res_out_proof                         true
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Options
% 3.05/0.99  
% 3.05/0.99  --superposition_flag                    true
% 3.05/0.99  --sup_passive_queue_type                priority_queues
% 3.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.99  --demod_completeness_check              fast
% 3.05/0.99  --demod_use_ground                      true
% 3.05/0.99  --sup_to_prop_solver                    passive
% 3.05/0.99  --sup_prop_simpl_new                    true
% 3.05/0.99  --sup_prop_simpl_given                  true
% 3.05/0.99  --sup_fun_splitting                     false
% 3.05/0.99  --sup_smt_interval                      50000
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Simplification Setup
% 3.05/0.99  
% 3.05/0.99  --sup_indices_passive                   []
% 3.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_full_bw                           [BwDemod]
% 3.05/0.99  --sup_immed_triv                        [TrivRules]
% 3.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_immed_bw_main                     []
% 3.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  
% 3.05/0.99  ------ Combination Options
% 3.05/0.99  
% 3.05/0.99  --comb_res_mult                         3
% 3.05/0.99  --comb_sup_mult                         2
% 3.05/0.99  --comb_inst_mult                        10
% 3.05/0.99  
% 3.05/0.99  ------ Debug Options
% 3.05/0.99  
% 3.05/0.99  --dbg_backtrace                         false
% 3.05/0.99  --dbg_dump_prop_clauses                 false
% 3.05/0.99  --dbg_dump_prop_clauses_file            -
% 3.05/0.99  --dbg_out_stat                          false
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  ------ Proving...
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  % SZS status Theorem for theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  fof(f6,axiom,(
% 3.05/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f17,plain,(
% 3.05/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 3.05/0.99    inference(ennf_transformation,[],[f6])).
% 3.05/0.99  
% 3.05/0.99  fof(f30,plain,(
% 3.05/0.99    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 3.05/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.05/0.99  
% 3.05/0.99  fof(f31,plain,(
% 3.05/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 3.05/0.99    inference(definition_folding,[],[f17,f30])).
% 3.05/0.99  
% 3.05/0.99  fof(f37,plain,(
% 3.05/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 3.05/0.99    inference(nnf_transformation,[],[f31])).
% 3.05/0.99  
% 3.05/0.99  fof(f64,plain,(
% 3.05/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 3.05/0.99    inference(cnf_transformation,[],[f37])).
% 3.05/0.99  
% 3.05/0.99  fof(f100,plain,(
% 3.05/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 3.05/0.99    inference(equality_resolution,[],[f64])).
% 3.05/0.99  
% 3.05/0.99  fof(f32,plain,(
% 3.05/0.99    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 3.05/0.99    inference(nnf_transformation,[],[f30])).
% 3.05/0.99  
% 3.05/0.99  fof(f33,plain,(
% 3.05/0.99    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 3.05/0.99    inference(flattening,[],[f32])).
% 3.05/0.99  
% 3.05/0.99  fof(f34,plain,(
% 3.05/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 3.05/0.99    inference(rectify,[],[f33])).
% 3.05/0.99  
% 3.05/0.99  fof(f35,plain,(
% 3.05/0.99    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f36,plain,(
% 3.05/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 3.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 3.05/0.99  
% 3.05/0.99  fof(f56,plain,(
% 3.05/0.99    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X0 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f36])).
% 3.05/0.99  
% 3.05/0.99  fof(f94,plain,(
% 3.05/0.99    ( ! [X6,X4,X2,X8,X5,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X8,X1,X2,X3,X4,X5,X6)) )),
% 3.05/0.99    inference(equality_resolution,[],[f56])).
% 3.05/0.99  
% 3.05/0.99  fof(f14,conjecture,(
% 3.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f15,negated_conjecture,(
% 3.05/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 3.05/0.99    inference(negated_conjecture,[],[f14])).
% 3.05/0.99  
% 3.05/0.99  fof(f16,plain,(
% 3.05/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 3.05/0.99    inference(rectify,[],[f15])).
% 3.05/0.99  
% 3.05/0.99  fof(f28,plain,(
% 3.05/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f16])).
% 3.05/0.99  
% 3.05/0.99  fof(f29,plain,(
% 3.05/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.05/0.99    inference(flattening,[],[f28])).
% 3.05/0.99  
% 3.05/0.99  fof(f43,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) => ((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(X0,X1,X2))))) )),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f42,plain,(
% 3.05/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,sK4)))) & ~r1_tsep_1(X1,sK4) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f41,plain,(
% 3.05/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,sK3,X2)))) & ~r1_tsep_1(sK3,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f40,plain,(
% 3.05/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f44,plain,(
% 3.05/0.99    ((((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) & ~r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f43,f42,f41,f40])).
% 3.05/0.99  
% 3.05/0.99  fof(f81,plain,(
% 3.05/0.99    m1_pre_topc(sK3,sK2)),
% 3.05/0.99    inference(cnf_transformation,[],[f44])).
% 3.05/0.99  
% 3.05/0.99  fof(f12,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f24,plain,(
% 3.05/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f12])).
% 3.05/0.99  
% 3.05/0.99  fof(f25,plain,(
% 3.05/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.99    inference(flattening,[],[f24])).
% 3.05/0.99  
% 3.05/0.99  fof(f74,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f25])).
% 3.05/0.99  
% 3.05/0.99  fof(f11,axiom,(
% 3.05/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)))))))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f22,plain,(
% 3.05/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f11])).
% 3.05/0.99  
% 3.05/0.99  fof(f23,plain,(
% 3.05/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.99    inference(flattening,[],[f22])).
% 3.05/0.99  
% 3.05/0.99  fof(f38,plain,(
% 3.05/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.99    inference(nnf_transformation,[],[f23])).
% 3.05/0.99  
% 3.05/0.99  fof(f70,plain,(
% 3.05/0.99    ( ! [X2,X0,X3,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f38])).
% 3.05/0.99  
% 3.05/0.99  fof(f7,axiom,(
% 3.05/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f66,plain,(
% 3.05/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f7])).
% 3.05/0.99  
% 3.05/0.99  fof(f2,axiom,(
% 3.05/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f46,plain,(
% 3.05/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f2])).
% 3.05/0.99  
% 3.05/0.99  fof(f3,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f47,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f3])).
% 3.05/0.99  
% 3.05/0.99  fof(f4,axiom,(
% 3.05/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f48,plain,(
% 3.05/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f4])).
% 3.05/0.99  
% 3.05/0.99  fof(f5,axiom,(
% 3.05/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f49,plain,(
% 3.05/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f5])).
% 3.05/0.99  
% 3.05/0.99  fof(f87,plain,(
% 3.05/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.05/0.99    inference(definition_unfolding,[],[f48,f49])).
% 3.05/0.99  
% 3.05/0.99  fof(f88,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.05/0.99    inference(definition_unfolding,[],[f47,f87])).
% 3.05/0.99  
% 3.05/0.99  fof(f89,plain,(
% 3.05/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.05/0.99    inference(definition_unfolding,[],[f46,f88])).
% 3.05/0.99  
% 3.05/0.99  fof(f90,plain,(
% 3.05/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.05/0.99    inference(definition_unfolding,[],[f66,f89])).
% 3.05/0.99  
% 3.05/0.99  fof(f93,plain,(
% 3.05/0.99    ( ! [X2,X0,X3,X1] : (k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.99    inference(definition_unfolding,[],[f70,f90])).
% 3.05/0.99  
% 3.05/0.99  fof(f101,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.99    inference(equality_resolution,[],[f93])).
% 3.05/0.99  
% 3.05/0.99  fof(f84,plain,(
% 3.05/0.99    ~r1_tsep_1(sK3,sK4)),
% 3.05/0.99    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  fof(f80,plain,(
% 3.05/1.00    ~v2_struct_0(sK3)),
% 3.05/1.00    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  fof(f82,plain,(
% 3.05/1.00    ~v2_struct_0(sK4)),
% 3.05/1.00    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  fof(f72,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f25])).
% 3.05/1.00  
% 3.05/1.00  fof(f73,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f25])).
% 3.05/1.00  
% 3.05/1.00  fof(f77,plain,(
% 3.05/1.00    ~v2_struct_0(sK2)),
% 3.05/1.00    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  fof(f79,plain,(
% 3.05/1.00    l1_pre_topc(sK2)),
% 3.05/1.00    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  fof(f83,plain,(
% 3.05/1.00    m1_pre_topc(sK4,sK2)),
% 3.05/1.00    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  fof(f8,axiom,(
% 3.05/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 3.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f18,plain,(
% 3.05/1.00    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 3.05/1.00    inference(ennf_transformation,[],[f8])).
% 3.05/1.00  
% 3.05/1.00  fof(f67,plain,(
% 3.05/1.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f18])).
% 3.05/1.00  
% 3.05/1.00  fof(f13,axiom,(
% 3.05/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f26,plain,(
% 3.05/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.05/1.00    inference(ennf_transformation,[],[f13])).
% 3.05/1.00  
% 3.05/1.00  fof(f27,plain,(
% 3.05/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.05/1.00    inference(flattening,[],[f26])).
% 3.05/1.00  
% 3.05/1.00  fof(f39,plain,(
% 3.05/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.05/1.00    inference(nnf_transformation,[],[f27])).
% 3.05/1.00  
% 3.05/1.00  fof(f75,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f39])).
% 3.05/1.00  
% 3.05/1.00  fof(f78,plain,(
% 3.05/1.00    v2_pre_topc(sK2)),
% 3.05/1.00    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  fof(f1,axiom,(
% 3.05/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f45,plain,(
% 3.05/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f1])).
% 3.05/1.00  
% 3.05/1.00  fof(f91,plain,(
% 3.05/1.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.05/1.00    inference(definition_unfolding,[],[f45,f90])).
% 3.05/1.00  
% 3.05/1.00  fof(f10,axiom,(
% 3.05/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f20,plain,(
% 3.05/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.05/1.00    inference(ennf_transformation,[],[f10])).
% 3.05/1.00  
% 3.05/1.00  fof(f21,plain,(
% 3.05/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/1.00    inference(flattening,[],[f20])).
% 3.05/1.00  
% 3.05/1.00  fof(f69,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f21])).
% 3.05/1.00  
% 3.05/1.00  fof(f9,axiom,(
% 3.05/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f19,plain,(
% 3.05/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.05/1.00    inference(ennf_transformation,[],[f9])).
% 3.05/1.00  
% 3.05/1.00  fof(f68,plain,(
% 3.05/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f19])).
% 3.05/1.00  
% 3.05/1.00  fof(f86,plain,(
% 3.05/1.00    ( ! [X4,X5] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 3.05/1.00    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  fof(f102,plain,(
% 3.05/1.00    ( ! [X5] : (~m1_subset_1(sK5,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 3.05/1.00    inference(equality_resolution,[],[f86])).
% 3.05/1.00  
% 3.05/1.00  fof(f103,plain,(
% 3.05/1.00    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.05/1.00    inference(equality_resolution,[],[f102])).
% 3.05/1.00  
% 3.05/1.00  fof(f85,plain,(
% 3.05/1.00    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))),
% 3.05/1.00    inference(cnf_transformation,[],[f44])).
% 3.05/1.00  
% 3.05/1.00  cnf(c_16,plain,
% 3.05/1.00      ( sP0(X0,X1,X2,X3,X4,X5,k4_enumset1(X5,X4,X3,X2,X1,X0)) ),
% 3.05/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6118,plain,
% 3.05/1.00      ( sP0(X0,X1,X2,X3,X4,X5,k4_enumset1(X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_8,plain,
% 3.05/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X0,X6) ),
% 3.05/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6126,plain,
% 3.05/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6) != iProver_top
% 3.05/1.00      | r2_hidden(X0,X6) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_8435,plain,
% 3.05/1.00      ( r2_hidden(X0,k4_enumset1(X1,X2,X3,X4,X5,X0)) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_6118,c_6126]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_32,negated_conjecture,
% 3.05/1.00      ( m1_pre_topc(sK3,sK2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6107,plain,
% 3.05/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_22,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X2,X1)
% 3.05/1.00      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 3.05/1.00      | v2_struct_0(X1)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(X2)
% 3.05/1.00      | ~ l1_pre_topc(X1) ),
% 3.05/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6114,plain,
% 3.05/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.05/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.05/1.00      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1) = iProver_top
% 3.05/1.00      | v2_struct_0(X1) = iProver_top
% 3.05/1.00      | v2_struct_0(X0) = iProver_top
% 3.05/1.00      | v2_struct_0(X2) = iProver_top
% 3.05/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_21,plain,
% 3.05/1.00      ( r1_tsep_1(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X0,X2)
% 3.05/1.00      | ~ m1_pre_topc(X1,X2)
% 3.05/1.00      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 3.05/1.00      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 3.05/1.00      | v2_struct_0(X2)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(X1)
% 3.05/1.00      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 3.05/1.00      | ~ l1_pre_topc(X2)
% 3.05/1.00      | k1_setfam_1(k4_enumset1(u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1))) = u1_struct_0(k2_tsep_1(X2,X0,X1)) ),
% 3.05/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_29,negated_conjecture,
% 3.05/1.00      ( ~ r1_tsep_1(sK3,sK4) ),
% 3.05/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_486,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X2,X1)
% 3.05/1.00      | ~ m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 3.05/1.00      | ~ v1_pre_topc(k2_tsep_1(X1,X2,X0))
% 3.05/1.00      | v2_struct_0(X2)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(X1)
% 3.05/1.00      | v2_struct_0(k2_tsep_1(X1,X2,X0))
% 3.05/1.00      | ~ l1_pre_topc(X1)
% 3.05/1.00      | k1_setfam_1(k4_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0))) = u1_struct_0(k2_tsep_1(X1,X2,X0))
% 3.05/1.00      | sK3 != X2
% 3.05/1.00      | sK4 != X0 ),
% 3.05/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_487,plain,
% 3.05/1.00      ( ~ m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0)
% 3.05/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.05/1.00      | ~ m1_pre_topc(sK4,X0)
% 3.05/1.00      | ~ v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | v2_struct_0(sK4)
% 3.05/1.00      | ~ l1_pre_topc(X0)
% 3.05/1.00      | k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4)) ),
% 3.05/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_33,negated_conjecture,
% 3.05/1.00      ( ~ v2_struct_0(sK3) ),
% 3.05/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_31,negated_conjecture,
% 3.05/1.00      ( ~ v2_struct_0(sK4) ),
% 3.05/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_491,plain,
% 3.05/1.00      ( ~ m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0)
% 3.05/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.05/1.00      | ~ m1_pre_topc(sK4,X0)
% 3.05/1.00      | ~ v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | ~ l1_pre_topc(X0)
% 3.05/1.00      | k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4)) ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_487,c_33,c_31]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6101,plain,
% 3.05/1.00      ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,X0) != iProver_top
% 3.05/1.00      | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) != iProver_top
% 3.05/1.00      | v2_struct_0(X0) = iProver_top
% 3.05/1.00      | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) = iProver_top
% 3.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_9807,plain,
% 3.05/1.00      ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,X0) != iProver_top
% 3.05/1.00      | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) != iProver_top
% 3.05/1.00      | v2_struct_0(X0) = iProver_top
% 3.05/1.00      | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) = iProver_top
% 3.05/1.00      | v2_struct_0(sK3) = iProver_top
% 3.05/1.00      | v2_struct_0(sK4) = iProver_top
% 3.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_6114,c_6101]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_40,plain,
% 3.05/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_42,plain,
% 3.05/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_24,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X2,X1)
% 3.05/1.00      | v2_struct_0(X1)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(X2)
% 3.05/1.00      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 3.05/1.00      | ~ l1_pre_topc(X1) ),
% 3.05/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6610,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(sK3,X1)
% 3.05/1.00      | v2_struct_0(X1)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | ~ v2_struct_0(k2_tsep_1(X1,sK3,X0))
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | ~ l1_pre_topc(X1) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6963,plain,
% 3.05/1.00      ( ~ m1_pre_topc(sK3,X0)
% 3.05/1.00      | ~ m1_pre_topc(sK4,X0)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | ~ v2_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | v2_struct_0(sK4)
% 3.05/1.00      | ~ l1_pre_topc(X0) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_6610]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6964,plain,
% 3.05/1.00      ( m1_pre_topc(sK3,X0) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,X0) != iProver_top
% 3.05/1.00      | v2_struct_0(X0) = iProver_top
% 3.05/1.00      | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) != iProver_top
% 3.05/1.00      | v2_struct_0(sK3) = iProver_top
% 3.05/1.00      | v2_struct_0(sK4) = iProver_top
% 3.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_6963]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_23,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X2,X1)
% 3.05/1.00      | v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 3.05/1.00      | v2_struct_0(X1)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(X2)
% 3.05/1.00      | ~ l1_pre_topc(X1) ),
% 3.05/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6611,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(sK3,X1)
% 3.05/1.00      | v1_pre_topc(k2_tsep_1(X1,sK3,X0))
% 3.05/1.00      | v2_struct_0(X1)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | ~ l1_pre_topc(X1) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6971,plain,
% 3.05/1.00      ( ~ m1_pre_topc(sK3,X0)
% 3.05/1.00      | ~ m1_pre_topc(sK4,X0)
% 3.05/1.00      | v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | v2_struct_0(sK4)
% 3.05/1.00      | ~ l1_pre_topc(X0) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_6611]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6972,plain,
% 3.05/1.00      ( m1_pre_topc(sK3,X0) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,X0) != iProver_top
% 3.05/1.00      | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) = iProver_top
% 3.05/1.00      | v2_struct_0(X0) = iProver_top
% 3.05/1.00      | v2_struct_0(sK3) = iProver_top
% 3.05/1.00      | v2_struct_0(sK4) = iProver_top
% 3.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_6971]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10285,plain,
% 3.05/1.00      ( v2_struct_0(X0) = iProver_top
% 3.05/1.00      | k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,X0) != iProver_top
% 3.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_9807,c_40,c_42,c_6964,c_6972]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10286,plain,
% 3.05/1.00      ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.05/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,X0) != iProver_top
% 3.05/1.00      | v2_struct_0(X0) = iProver_top
% 3.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.05/1.00      inference(renaming,[status(thm)],[c_10285]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10296,plain,
% 3.05/1.00      ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.05/1.00      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.05/1.00      | v2_struct_0(sK2) = iProver_top
% 3.05/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_6107,c_10286]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_36,negated_conjecture,
% 3.05/1.00      ( ~ v2_struct_0(sK2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_34,negated_conjecture,
% 3.05/1.00      ( l1_pre_topc(sK2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_30,negated_conjecture,
% 3.05/1.00      ( m1_pre_topc(sK4,sK2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_494,plain,
% 3.05/1.00      ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK3,sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK4,sK2)
% 3.05/1.00      | ~ v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
% 3.05/1.00      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.05/1.00      | v2_struct_0(sK2)
% 3.05/1.00      | ~ l1_pre_topc(sK2)
% 3.05/1.00      | k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_491]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6495,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK3,sK2)
% 3.05/1.00      | v1_pre_topc(k2_tsep_1(sK2,sK3,X0))
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(sK2)
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | ~ l1_pre_topc(sK2) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6649,plain,
% 3.05/1.00      ( ~ m1_pre_topc(sK3,sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK4,sK2)
% 3.05/1.00      | v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
% 3.05/1.00      | v2_struct_0(sK2)
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | v2_struct_0(sK4)
% 3.05/1.00      | ~ l1_pre_topc(sK2) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_6495]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6509,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK3,sK2)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | ~ v2_struct_0(k2_tsep_1(sK2,sK3,X0))
% 3.05/1.00      | v2_struct_0(sK2)
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | ~ l1_pre_topc(sK2) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6670,plain,
% 3.05/1.00      ( ~ m1_pre_topc(sK3,sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK4,sK2)
% 3.05/1.00      | ~ v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.05/1.00      | v2_struct_0(sK2)
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | v2_struct_0(sK4)
% 3.05/1.00      | ~ l1_pre_topc(sK2) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_6509]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6519,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,sK2)
% 3.05/1.00      | m1_pre_topc(k2_tsep_1(sK2,sK3,X0),sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK3,sK2)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(sK2)
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | ~ l1_pre_topc(sK2) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6790,plain,
% 3.05/1.00      ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK3,sK2)
% 3.05/1.00      | ~ m1_pre_topc(sK4,sK2)
% 3.05/1.00      | v2_struct_0(sK2)
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | v2_struct_0(sK4)
% 3.05/1.00      | ~ l1_pre_topc(sK2) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_6519]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10861,plain,
% 3.05/1.00      ( k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_10296,c_36,c_34,c_33,c_32,c_31,c_30,c_494,c_6649,
% 3.05/1.00                 c_6670,c_6790]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_17,plain,
% 3.05/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6117,plain,
% 3.05/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.05/1.00      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10918,plain,
% 3.05/1.00      ( r2_hidden(X0,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top
% 3.05/1.00      | r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X0) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_10861,c_6117]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_11099,plain,
% 3.05/1.00      ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_8435,c_10918]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_26,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X2,X1)
% 3.05/1.00      | m1_pre_topc(X0,X2)
% 3.05/1.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.05/1.00      | ~ v2_pre_topc(X1)
% 3.05/1.00      | ~ l1_pre_topc(X1) ),
% 3.05/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_35,negated_conjecture,
% 3.05/1.00      ( v2_pre_topc(sK2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_387,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X2,X1)
% 3.05/1.00      | m1_pre_topc(X0,X2)
% 3.05/1.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.05/1.00      | ~ l1_pre_topc(X1)
% 3.05/1.00      | sK2 != X1 ),
% 3.05/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_388,plain,
% 3.05/1.00      ( m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X1,sK2)
% 3.05/1.00      | ~ m1_pre_topc(X0,sK2)
% 3.05/1.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.05/1.00      | ~ l1_pre_topc(sK2) ),
% 3.05/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_390,plain,
% 3.05/1.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.05/1.00      | ~ m1_pre_topc(X0,sK2)
% 3.05/1.00      | ~ m1_pre_topc(X1,sK2)
% 3.05/1.00      | m1_pre_topc(X0,X1) ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_388,c_34]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_391,plain,
% 3.05/1.00      ( m1_pre_topc(X0,X1)
% 3.05/1.00      | ~ m1_pre_topc(X0,sK2)
% 3.05/1.00      | ~ m1_pre_topc(X1,sK2)
% 3.05/1.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.05/1.00      inference(renaming,[status(thm)],[c_390]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6103,plain,
% 3.05/1.00      ( m1_pre_topc(X0,X1) = iProver_top
% 3.05/1.00      | m1_pre_topc(X1,sK2) != iProver_top
% 3.05/1.00      | m1_pre_topc(X0,sK2) != iProver_top
% 3.05/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_11580,plain,
% 3.05/1.00      ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
% 3.05/1.00      | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4) = iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,sK2) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_11099,c_6103]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_0,plain,
% 3.05/1.00      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6134,plain,
% 3.05/1.00      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10917,plain,
% 3.05/1.00      ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3)) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_10861,c_6134]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10931,plain,
% 3.05/1.00      ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
% 3.05/1.00      | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) = iProver_top
% 3.05/1.00      | m1_pre_topc(sK3,sK2) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_10917,c_6103]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_19,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.05/1.00      | m1_subset_1(X0,u1_struct_0(X2))
% 3.05/1.00      | ~ m1_pre_topc(X1,X2)
% 3.05/1.00      | v2_struct_0(X2)
% 3.05/1.00      | v2_struct_0(X1)
% 3.05/1.00      | ~ l1_pre_topc(X2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_9780,plain,
% 3.05/1.00      ( m1_subset_1(sK5,u1_struct_0(X0))
% 3.05/1.00      | ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
% 3.05/1.00      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
% 3.05/1.00      | v2_struct_0(X0)
% 3.05/1.00      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.05/1.00      | ~ l1_pre_topc(X0) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10827,plain,
% 3.05/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
% 3.05/1.00      | m1_subset_1(sK5,u1_struct_0(sK4))
% 3.05/1.00      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4)
% 3.05/1.00      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.05/1.00      | v2_struct_0(sK4)
% 3.05/1.00      | ~ l1_pre_topc(sK4) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_9780]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10830,plain,
% 3.05/1.00      ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) != iProver_top
% 3.05/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top
% 3.05/1.00      | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4) != iProver_top
% 3.05/1.00      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.05/1.00      | v2_struct_0(sK4) = iProver_top
% 3.05/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_10827]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10821,plain,
% 3.05/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
% 3.05/1.00      | m1_subset_1(sK5,u1_struct_0(sK3))
% 3.05/1.00      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
% 3.05/1.00      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.05/1.00      | v2_struct_0(sK3)
% 3.05/1.00      | ~ l1_pre_topc(sK3) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_9780]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10822,plain,
% 3.05/1.00      ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) != iProver_top
% 3.05/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top
% 3.05/1.00      | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) != iProver_top
% 3.05/1.00      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.05/1.00      | v2_struct_0(sK3) = iProver_top
% 3.05/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_10821]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6791,plain,
% 3.05/1.00      ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) = iProver_top
% 3.05/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.05/1.00      | v2_struct_0(sK2) = iProver_top
% 3.05/1.00      | v2_struct_0(sK3) = iProver_top
% 3.05/1.00      | v2_struct_0(sK4) = iProver_top
% 3.05/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_6790]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_18,plain,
% 3.05/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6116,plain,
% 3.05/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.05/1.00      | l1_pre_topc(X1) != iProver_top
% 3.05/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6765,plain,
% 3.05/1.00      ( l1_pre_topc(sK2) != iProver_top
% 3.05/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_6107,c_6116]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6109,plain,
% 3.05/1.00      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6764,plain,
% 3.05/1.00      ( l1_pre_topc(sK2) != iProver_top
% 3.05/1.00      | l1_pre_topc(sK4) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_6109,c_6116]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6671,plain,
% 3.05/1.00      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.05/1.00      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.05/1.00      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.05/1.00      | v2_struct_0(sK2) = iProver_top
% 3.05/1.00      | v2_struct_0(sK3) = iProver_top
% 3.05/1.00      | v2_struct_0(sK4) = iProver_top
% 3.05/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_6670]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_27,negated_conjecture,
% 3.05/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.05/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.05/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_46,plain,
% 3.05/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.05/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_28,negated_conjecture,
% 3.05/1.00      ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
% 3.05/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_45,plain,
% 3.05/1.00      ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_43,plain,
% 3.05/1.00      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_41,plain,
% 3.05/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_39,plain,
% 3.05/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_37,plain,
% 3.05/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(contradiction,plain,
% 3.05/1.00      ( $false ),
% 3.05/1.00      inference(minisat,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_11580,c_10931,c_10830,c_10822,c_6791,c_6765,c_6764,
% 3.05/1.00                 c_6671,c_46,c_45,c_43,c_42,c_41,c_40,c_39,c_37]) ).
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/1.00  
% 3.05/1.00  ------                               Statistics
% 3.05/1.00  
% 3.05/1.00  ------ General
% 3.05/1.00  
% 3.05/1.00  abstr_ref_over_cycles:                  0
% 3.05/1.00  abstr_ref_under_cycles:                 0
% 3.05/1.00  gc_basic_clause_elim:                   0
% 3.05/1.00  forced_gc_time:                         0
% 3.05/1.00  parsing_time:                           0.011
% 3.05/1.00  unif_index_cands_time:                  0.
% 3.05/1.00  unif_index_add_time:                    0.
% 3.05/1.00  orderings_time:                         0.
% 3.05/1.00  out_proof_time:                         0.01
% 3.05/1.00  total_time:                             0.276
% 3.05/1.00  num_of_symbols:                         47
% 3.05/1.00  num_of_terms:                           7035
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing
% 3.05/1.00  
% 3.05/1.00  num_of_splits:                          0
% 3.05/1.00  num_of_split_atoms:                     0
% 3.05/1.00  num_of_reused_defs:                     0
% 3.05/1.00  num_eq_ax_congr_red:                    42
% 3.05/1.00  num_of_sem_filtered_clauses:            1
% 3.05/1.00  num_of_subtypes:                        0
% 3.05/1.00  monotx_restored_types:                  0
% 3.05/1.00  sat_num_of_epr_types:                   0
% 3.05/1.00  sat_num_of_non_cyclic_types:            0
% 3.05/1.00  sat_guarded_non_collapsed_types:        0
% 3.05/1.00  num_pure_diseq_elim:                    0
% 3.05/1.00  simp_replaced_by:                       0
% 3.05/1.00  res_preprocessed:                       171
% 3.05/1.00  prep_upred:                             0
% 3.05/1.00  prep_unflattend:                        324
% 3.05/1.00  smt_new_axioms:                         0
% 3.05/1.00  pred_elim_cands:                        8
% 3.05/1.00  pred_elim:                              2
% 3.05/1.00  pred_elim_cl:                           2
% 3.05/1.00  pred_elim_cycles:                       10
% 3.05/1.00  merged_defs:                            0
% 3.05/1.00  merged_defs_ncl:                        0
% 3.05/1.00  bin_hyper_res:                          0
% 3.05/1.00  prep_cycles:                            4
% 3.05/1.00  pred_elim_time:                         0.065
% 3.05/1.00  splitting_time:                         0.
% 3.05/1.00  sem_filter_time:                        0.
% 3.05/1.00  monotx_time:                            0.
% 3.05/1.00  subtype_inf_time:                       0.
% 3.05/1.00  
% 3.05/1.00  ------ Problem properties
% 3.05/1.00  
% 3.05/1.00  clauses:                                35
% 3.05/1.00  conjectures:                            8
% 3.05/1.00  epr:                                    14
% 3.05/1.00  horn:                                   27
% 3.05/1.00  ground:                                 8
% 3.05/1.00  unary:                                  9
% 3.05/1.00  binary:                                 9
% 3.05/1.00  lits:                                   116
% 3.05/1.00  lits_eq:                                22
% 3.05/1.00  fd_pure:                                0
% 3.05/1.00  fd_pseudo:                              0
% 3.05/1.00  fd_cond:                                0
% 3.05/1.00  fd_pseudo_cond:                         3
% 3.05/1.00  ac_symbols:                             0
% 3.05/1.00  
% 3.05/1.00  ------ Propositional Solver
% 3.05/1.00  
% 3.05/1.00  prop_solver_calls:                      28
% 3.05/1.00  prop_fast_solver_calls:                 2506
% 3.05/1.00  smt_solver_calls:                       0
% 3.05/1.00  smt_fast_solver_calls:                  0
% 3.05/1.00  prop_num_of_clauses:                    2894
% 3.05/1.00  prop_preprocess_simplified:             11380
% 3.05/1.00  prop_fo_subsumed:                       39
% 3.05/1.00  prop_solver_time:                       0.
% 3.05/1.00  smt_solver_time:                        0.
% 3.05/1.00  smt_fast_solver_time:                   0.
% 3.05/1.00  prop_fast_solver_time:                  0.
% 3.05/1.00  prop_unsat_core_time:                   0.
% 3.05/1.00  
% 3.05/1.00  ------ QBF
% 3.05/1.00  
% 3.05/1.00  qbf_q_res:                              0
% 3.05/1.00  qbf_num_tautologies:                    0
% 3.05/1.00  qbf_prep_cycles:                        0
% 3.05/1.00  
% 3.05/1.00  ------ BMC1
% 3.05/1.00  
% 3.05/1.00  bmc1_current_bound:                     -1
% 3.05/1.00  bmc1_last_solved_bound:                 -1
% 3.05/1.00  bmc1_unsat_core_size:                   -1
% 3.05/1.00  bmc1_unsat_core_parents_size:           -1
% 3.05/1.00  bmc1_merge_next_fun:                    0
% 3.05/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.05/1.00  
% 3.05/1.00  ------ Instantiation
% 3.05/1.00  
% 3.05/1.00  inst_num_of_clauses:                    947
% 3.05/1.00  inst_num_in_passive:                    558
% 3.05/1.00  inst_num_in_active:                     306
% 3.05/1.00  inst_num_in_unprocessed:                83
% 3.05/1.00  inst_num_of_loops:                      340
% 3.05/1.00  inst_num_of_learning_restarts:          0
% 3.05/1.00  inst_num_moves_active_passive:          32
% 3.05/1.00  inst_lit_activity:                      0
% 3.05/1.00  inst_lit_activity_moves:                1
% 3.05/1.00  inst_num_tautologies:                   0
% 3.05/1.00  inst_num_prop_implied:                  0
% 3.05/1.00  inst_num_existing_simplified:           0
% 3.05/1.00  inst_num_eq_res_simplified:             0
% 3.05/1.00  inst_num_child_elim:                    0
% 3.05/1.00  inst_num_of_dismatching_blockings:      109
% 3.05/1.00  inst_num_of_non_proper_insts:           535
% 3.05/1.00  inst_num_of_duplicates:                 0
% 3.05/1.00  inst_inst_num_from_inst_to_res:         0
% 3.05/1.00  inst_dismatching_checking_time:         0.
% 3.05/1.00  
% 3.05/1.00  ------ Resolution
% 3.05/1.00  
% 3.05/1.00  res_num_of_clauses:                     0
% 3.05/1.00  res_num_in_passive:                     0
% 3.05/1.00  res_num_in_active:                      0
% 3.05/1.00  res_num_of_loops:                       175
% 3.05/1.00  res_forward_subset_subsumed:            12
% 3.05/1.00  res_backward_subset_subsumed:           0
% 3.05/1.00  res_forward_subsumed:                   0
% 3.05/1.00  res_backward_subsumed:                  0
% 3.05/1.00  res_forward_subsumption_resolution:     0
% 3.05/1.00  res_backward_subsumption_resolution:    0
% 3.05/1.00  res_clause_to_clause_subsumption:       3285
% 3.05/1.00  res_orphan_elimination:                 0
% 3.05/1.00  res_tautology_del:                      33
% 3.05/1.00  res_num_eq_res_simplified:              0
% 3.05/1.00  res_num_sel_changes:                    0
% 3.05/1.00  res_moves_from_active_to_pass:          0
% 3.05/1.00  
% 3.05/1.00  ------ Superposition
% 3.05/1.00  
% 3.05/1.00  sup_time_total:                         0.
% 3.05/1.00  sup_time_generating:                    0.
% 3.05/1.00  sup_time_sim_full:                      0.
% 3.05/1.00  sup_time_sim_immed:                     0.
% 3.05/1.00  
% 3.05/1.00  sup_num_of_clauses:                     71
% 3.05/1.00  sup_num_in_active:                      64
% 3.05/1.00  sup_num_in_passive:                     7
% 3.05/1.00  sup_num_of_loops:                       67
% 3.05/1.00  sup_fw_superposition:                   36
% 3.05/1.00  sup_bw_superposition:                   19
% 3.05/1.00  sup_immediate_simplified:               8
% 3.05/1.00  sup_given_eliminated:                   0
% 3.05/1.00  comparisons_done:                       0
% 3.05/1.00  comparisons_avoided:                    0
% 3.05/1.00  
% 3.05/1.00  ------ Simplifications
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  sim_fw_subset_subsumed:                 6
% 3.05/1.00  sim_bw_subset_subsumed:                 1
% 3.05/1.00  sim_fw_subsumed:                        1
% 3.05/1.00  sim_bw_subsumed:                        1
% 3.05/1.00  sim_fw_subsumption_res:                 4
% 3.05/1.00  sim_bw_subsumption_res:                 0
% 3.05/1.00  sim_tautology_del:                      1
% 3.05/1.00  sim_eq_tautology_del:                   5
% 3.05/1.00  sim_eq_res_simp:                        0
% 3.05/1.00  sim_fw_demodulated:                     0
% 3.05/1.00  sim_bw_demodulated:                     3
% 3.05/1.00  sim_light_normalised:                   0
% 3.05/1.00  sim_joinable_taut:                      0
% 3.05/1.00  sim_joinable_simp:                      0
% 3.05/1.00  sim_ac_normalised:                      0
% 3.05/1.00  sim_smt_subsumption:                    0
% 3.05/1.00  
%------------------------------------------------------------------------------

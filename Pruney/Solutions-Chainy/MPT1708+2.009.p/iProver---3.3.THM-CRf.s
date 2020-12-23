%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:50 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 877 expanded)
%              Number of clauses        :   80 ( 177 expanded)
%              Number of leaves         :   21 ( 280 expanded)
%              Depth                    :   22
%              Number of atoms          :  929 (8684 expanded)
%              Number of equality atoms :  357 (1767 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ),
    inference(definition_folding,[],[f18,f31])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) )
      & ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP0(X6,X5,X4,X3,X2,X1,X0,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f68])).

fof(f33,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f34,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8
                & X6 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | X6 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ( X0 != X8
              & X1 != X8
              & X2 != X8
              & X3 != X8
              & X4 != X8
              & X5 != X8
              & X6 != X8 )
            | ~ r2_hidden(X8,X7) )
          & ( X0 = X8
            | X1 = X8
            | X2 = X8
            | X3 = X8
            | X4 = X8
            | X5 = X8
            | X6 = X8
            | r2_hidden(X8,X7) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | X0 != X9
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | ~ sP0(X9,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(equality_resolution,[],[f59])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f44,f43,f42,f41])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f91])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f92])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f93])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f94])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(X3)
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
    inference(definition_unfolding,[],[f74,f95])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(k2_tsep_1(X0,X1,X2))
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
    inference(equality_resolution,[],[f98])).

fof(f88,plain,(
    ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f46,f95])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    ! [X4,X5] :
      ( sK5 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f108,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f109,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f108])).

fof(f89,plain,(
    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X6,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_7496,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X6,X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | r2_hidden(X0,X7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_7505,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7) != iProver_top
    | r2_hidden(X0,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10229,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7496,c_7505])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7485,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_7492,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,plain,
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
    | k1_setfam_1(k5_enumset1(u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1))) = u1_struct_0(k2_tsep_1(X2,X0,X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_505,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ v1_pre_topc(k2_tsep_1(X1,X2,X0))
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | k1_setfam_1(k5_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0))) = u1_struct_0(k2_tsep_1(X1,X2,X0))
    | sK3 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_506,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_510,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
    | ~ l1_pre_topc(X0)
    | k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_35,c_33])).

cnf(c_7479,plain,
    ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
    | m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_11289,plain,
    ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7492,c_7479])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8009,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_8468,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK4,X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_8009])).

cnf(c_8469,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8468])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8010,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK3,X1)
    | v1_pre_topc(k2_tsep_1(X1,sK3,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_8478,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK4,X0)
    | v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_8010])).

cnf(c_8479,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8478])).

cnf(c_12382,plain,
    ( v2_struct_0(X0) = iProver_top
    | k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11289,c_42,c_44,c_8469,c_8479])).

cnf(c_12383,plain,
    ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12382])).

cnf(c_12393,plain,
    ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7485,c_12383])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_513,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_7893,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v1_pre_topc(k2_tsep_1(sK2,sK3,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_8066,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7893])).

cnf(c_7907,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK2,sK3,X0))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_8082,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7907])).

cnf(c_7917,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_pre_topc(k2_tsep_1(sK2,sK3,X0),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_8298,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7917])).

cnf(c_12396,plain,
    ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12393,c_38,c_36,c_35,c_34,c_33,c_32,c_513,c_8066,c_8082,c_8298])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7495,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12453,plain,
    ( r2_hidden(X0,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top
    | r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12396,c_7495])).

cnf(c_12556,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10229,c_12453])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_406,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_407,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_409,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_36])).

cnf(c_410,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_409])).

cnf(c_7481,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_13040,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12556,c_7481])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_7514,plain,
    ( r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12452,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12396,c_7514])).

cnf(c_12499,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12452,c_7481])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_11215,plain,
    ( m1_subset_1(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_12187,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    | m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11215])).

cnf(c_12190,plain,
    ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12187])).

cnf(c_12181,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    | m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_11215])).

cnf(c_12182,plain,
    ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12181])).

cnf(c_8299,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8298])).

cnf(c_8083,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8082])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7494,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8047,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7485,c_7494])).

cnf(c_7487,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8046,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7487,c_7494])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_45,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_43,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13040,c_12499,c_12190,c_12182,c_8299,c_8083,c_8047,c_8046,c_48,c_47,c_45,c_44,c_43,c_42,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.40/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/1.00  
% 3.40/1.00  ------  iProver source info
% 3.40/1.00  
% 3.40/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.40/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/1.00  git: non_committed_changes: false
% 3.40/1.00  git: last_make_outside_of_git: false
% 3.40/1.00  
% 3.40/1.00  ------ 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options
% 3.40/1.00  
% 3.40/1.00  --out_options                           all
% 3.40/1.00  --tptp_safe_out                         true
% 3.40/1.00  --problem_path                          ""
% 3.40/1.00  --include_path                          ""
% 3.40/1.00  --clausifier                            res/vclausify_rel
% 3.40/1.00  --clausifier_options                    --mode clausify
% 3.40/1.00  --stdin                                 false
% 3.40/1.00  --stats_out                             all
% 3.40/1.00  
% 3.40/1.00  ------ General Options
% 3.40/1.00  
% 3.40/1.00  --fof                                   false
% 3.40/1.00  --time_out_real                         305.
% 3.40/1.00  --time_out_virtual                      -1.
% 3.40/1.00  --symbol_type_check                     false
% 3.40/1.00  --clausify_out                          false
% 3.40/1.00  --sig_cnt_out                           false
% 3.40/1.00  --trig_cnt_out                          false
% 3.40/1.00  --trig_cnt_out_tolerance                1.
% 3.40/1.00  --trig_cnt_out_sk_spl                   false
% 3.40/1.00  --abstr_cl_out                          false
% 3.40/1.00  
% 3.40/1.00  ------ Global Options
% 3.40/1.00  
% 3.40/1.00  --schedule                              default
% 3.40/1.00  --add_important_lit                     false
% 3.40/1.00  --prop_solver_per_cl                    1000
% 3.40/1.00  --min_unsat_core                        false
% 3.40/1.00  --soft_assumptions                      false
% 3.40/1.00  --soft_lemma_size                       3
% 3.40/1.00  --prop_impl_unit_size                   0
% 3.40/1.00  --prop_impl_unit                        []
% 3.40/1.00  --share_sel_clauses                     true
% 3.40/1.00  --reset_solvers                         false
% 3.40/1.00  --bc_imp_inh                            [conj_cone]
% 3.40/1.00  --conj_cone_tolerance                   3.
% 3.40/1.00  --extra_neg_conj                        none
% 3.40/1.00  --large_theory_mode                     true
% 3.40/1.00  --prolific_symb_bound                   200
% 3.40/1.00  --lt_threshold                          2000
% 3.40/1.00  --clause_weak_htbl                      true
% 3.40/1.00  --gc_record_bc_elim                     false
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing Options
% 3.40/1.00  
% 3.40/1.00  --preprocessing_flag                    true
% 3.40/1.00  --time_out_prep_mult                    0.1
% 3.40/1.00  --splitting_mode                        input
% 3.40/1.00  --splitting_grd                         true
% 3.40/1.00  --splitting_cvd                         false
% 3.40/1.00  --splitting_cvd_svl                     false
% 3.40/1.00  --splitting_nvd                         32
% 3.40/1.00  --sub_typing                            true
% 3.40/1.00  --prep_gs_sim                           true
% 3.40/1.00  --prep_unflatten                        true
% 3.40/1.00  --prep_res_sim                          true
% 3.40/1.00  --prep_upred                            true
% 3.40/1.00  --prep_sem_filter                       exhaustive
% 3.40/1.00  --prep_sem_filter_out                   false
% 3.40/1.00  --pred_elim                             true
% 3.40/1.00  --res_sim_input                         true
% 3.40/1.00  --eq_ax_congr_red                       true
% 3.40/1.00  --pure_diseq_elim                       true
% 3.40/1.00  --brand_transform                       false
% 3.40/1.00  --non_eq_to_eq                          false
% 3.40/1.00  --prep_def_merge                        true
% 3.40/1.00  --prep_def_merge_prop_impl              false
% 3.40/1.00  --prep_def_merge_mbd                    true
% 3.40/1.00  --prep_def_merge_tr_red                 false
% 3.40/1.00  --prep_def_merge_tr_cl                  false
% 3.40/1.00  --smt_preprocessing                     true
% 3.40/1.00  --smt_ac_axioms                         fast
% 3.40/1.00  --preprocessed_out                      false
% 3.40/1.00  --preprocessed_stats                    false
% 3.40/1.00  
% 3.40/1.00  ------ Abstraction refinement Options
% 3.40/1.00  
% 3.40/1.00  --abstr_ref                             []
% 3.40/1.00  --abstr_ref_prep                        false
% 3.40/1.00  --abstr_ref_until_sat                   false
% 3.40/1.00  --abstr_ref_sig_restrict                funpre
% 3.40/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.00  --abstr_ref_under                       []
% 3.40/1.00  
% 3.40/1.00  ------ SAT Options
% 3.40/1.00  
% 3.40/1.00  --sat_mode                              false
% 3.40/1.00  --sat_fm_restart_options                ""
% 3.40/1.00  --sat_gr_def                            false
% 3.40/1.00  --sat_epr_types                         true
% 3.40/1.00  --sat_non_cyclic_types                  false
% 3.40/1.00  --sat_finite_models                     false
% 3.40/1.00  --sat_fm_lemmas                         false
% 3.40/1.00  --sat_fm_prep                           false
% 3.40/1.00  --sat_fm_uc_incr                        true
% 3.40/1.00  --sat_out_model                         small
% 3.40/1.00  --sat_out_clauses                       false
% 3.40/1.00  
% 3.40/1.00  ------ QBF Options
% 3.40/1.00  
% 3.40/1.00  --qbf_mode                              false
% 3.40/1.00  --qbf_elim_univ                         false
% 3.40/1.00  --qbf_dom_inst                          none
% 3.40/1.00  --qbf_dom_pre_inst                      false
% 3.40/1.00  --qbf_sk_in                             false
% 3.40/1.00  --qbf_pred_elim                         true
% 3.40/1.00  --qbf_split                             512
% 3.40/1.00  
% 3.40/1.00  ------ BMC1 Options
% 3.40/1.00  
% 3.40/1.00  --bmc1_incremental                      false
% 3.40/1.00  --bmc1_axioms                           reachable_all
% 3.40/1.00  --bmc1_min_bound                        0
% 3.40/1.00  --bmc1_max_bound                        -1
% 3.40/1.00  --bmc1_max_bound_default                -1
% 3.40/1.00  --bmc1_symbol_reachability              true
% 3.40/1.00  --bmc1_property_lemmas                  false
% 3.40/1.00  --bmc1_k_induction                      false
% 3.40/1.00  --bmc1_non_equiv_states                 false
% 3.40/1.00  --bmc1_deadlock                         false
% 3.40/1.00  --bmc1_ucm                              false
% 3.40/1.00  --bmc1_add_unsat_core                   none
% 3.40/1.00  --bmc1_unsat_core_children              false
% 3.40/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.00  --bmc1_out_stat                         full
% 3.40/1.00  --bmc1_ground_init                      false
% 3.40/1.00  --bmc1_pre_inst_next_state              false
% 3.40/1.00  --bmc1_pre_inst_state                   false
% 3.40/1.00  --bmc1_pre_inst_reach_state             false
% 3.40/1.00  --bmc1_out_unsat_core                   false
% 3.40/1.00  --bmc1_aig_witness_out                  false
% 3.40/1.00  --bmc1_verbose                          false
% 3.40/1.00  --bmc1_dump_clauses_tptp                false
% 3.40/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.00  --bmc1_dump_file                        -
% 3.40/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.00  --bmc1_ucm_extend_mode                  1
% 3.40/1.00  --bmc1_ucm_init_mode                    2
% 3.40/1.00  --bmc1_ucm_cone_mode                    none
% 3.40/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.00  --bmc1_ucm_relax_model                  4
% 3.40/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.00  --bmc1_ucm_layered_model                none
% 3.40/1.00  --bmc1_ucm_max_lemma_size               10
% 3.40/1.00  
% 3.40/1.00  ------ AIG Options
% 3.40/1.00  
% 3.40/1.00  --aig_mode                              false
% 3.40/1.00  
% 3.40/1.00  ------ Instantiation Options
% 3.40/1.00  
% 3.40/1.00  --instantiation_flag                    true
% 3.40/1.00  --inst_sos_flag                         false
% 3.40/1.00  --inst_sos_phase                        true
% 3.40/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel_side                     num_symb
% 3.40/1.00  --inst_solver_per_active                1400
% 3.40/1.00  --inst_solver_calls_frac                1.
% 3.40/1.00  --inst_passive_queue_type               priority_queues
% 3.40/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.00  --inst_passive_queues_freq              [25;2]
% 3.40/1.00  --inst_dismatching                      true
% 3.40/1.00  --inst_eager_unprocessed_to_passive     true
% 3.40/1.00  --inst_prop_sim_given                   true
% 3.40/1.00  --inst_prop_sim_new                     false
% 3.40/1.00  --inst_subs_new                         false
% 3.40/1.00  --inst_eq_res_simp                      false
% 3.40/1.00  --inst_subs_given                       false
% 3.40/1.00  --inst_orphan_elimination               true
% 3.40/1.00  --inst_learning_loop_flag               true
% 3.40/1.00  --inst_learning_start                   3000
% 3.40/1.00  --inst_learning_factor                  2
% 3.40/1.00  --inst_start_prop_sim_after_learn       3
% 3.40/1.00  --inst_sel_renew                        solver
% 3.40/1.00  --inst_lit_activity_flag                true
% 3.40/1.00  --inst_restr_to_given                   false
% 3.40/1.00  --inst_activity_threshold               500
% 3.40/1.00  --inst_out_proof                        true
% 3.40/1.00  
% 3.40/1.00  ------ Resolution Options
% 3.40/1.00  
% 3.40/1.00  --resolution_flag                       true
% 3.40/1.00  --res_lit_sel                           adaptive
% 3.40/1.00  --res_lit_sel_side                      none
% 3.40/1.00  --res_ordering                          kbo
% 3.40/1.00  --res_to_prop_solver                    active
% 3.40/1.00  --res_prop_simpl_new                    false
% 3.40/1.00  --res_prop_simpl_given                  true
% 3.40/1.00  --res_passive_queue_type                priority_queues
% 3.40/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.00  --res_passive_queues_freq               [15;5]
% 3.40/1.00  --res_forward_subs                      full
% 3.40/1.00  --res_backward_subs                     full
% 3.40/1.00  --res_forward_subs_resolution           true
% 3.40/1.00  --res_backward_subs_resolution          true
% 3.40/1.00  --res_orphan_elimination                true
% 3.40/1.00  --res_time_limit                        2.
% 3.40/1.00  --res_out_proof                         true
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Options
% 3.40/1.00  
% 3.40/1.00  --superposition_flag                    true
% 3.40/1.00  --sup_passive_queue_type                priority_queues
% 3.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.40/1.00  --demod_completeness_check              fast
% 3.40/1.00  --demod_use_ground                      true
% 3.40/1.00  --sup_to_prop_solver                    passive
% 3.40/1.00  --sup_prop_simpl_new                    true
% 3.40/1.00  --sup_prop_simpl_given                  true
% 3.40/1.00  --sup_fun_splitting                     false
% 3.40/1.00  --sup_smt_interval                      50000
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Simplification Setup
% 3.40/1.00  
% 3.40/1.00  --sup_indices_passive                   []
% 3.40/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_full_bw                           [BwDemod]
% 3.40/1.00  --sup_immed_triv                        [TrivRules]
% 3.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_immed_bw_main                     []
% 3.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.00  
% 3.40/1.00  ------ Combination Options
% 3.40/1.00  
% 3.40/1.00  --comb_res_mult                         3
% 3.40/1.00  --comb_sup_mult                         2
% 3.40/1.00  --comb_inst_mult                        10
% 3.40/1.00  
% 3.40/1.00  ------ Debug Options
% 3.40/1.00  
% 3.40/1.00  --dbg_backtrace                         false
% 3.40/1.00  --dbg_dump_prop_clauses                 false
% 3.40/1.00  --dbg_dump_prop_clauses_file            -
% 3.40/1.00  --dbg_out_stat                          false
% 3.40/1.00  ------ Parsing...
% 3.40/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/1.00  ------ Proving...
% 3.40/1.00  ------ Problem Properties 
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  clauses                                 37
% 3.40/1.00  conjectures                             8
% 3.40/1.00  EPR                                     15
% 3.40/1.00  Horn                                    29
% 3.40/1.00  unary                                   9
% 3.40/1.00  binary                                  10
% 3.40/1.00  lits                                    123
% 3.40/1.00  lits eq                                 25
% 3.40/1.00  fd_pure                                 0
% 3.40/1.00  fd_pseudo                               0
% 3.40/1.00  fd_cond                                 0
% 3.40/1.00  fd_pseudo_cond                          3
% 3.40/1.00  AC symbols                              0
% 3.40/1.00  
% 3.40/1.00  ------ Schedule dynamic 5 is on 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  ------ 
% 3.40/1.00  Current options:
% 3.40/1.00  ------ 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options
% 3.40/1.00  
% 3.40/1.00  --out_options                           all
% 3.40/1.00  --tptp_safe_out                         true
% 3.40/1.00  --problem_path                          ""
% 3.40/1.00  --include_path                          ""
% 3.40/1.00  --clausifier                            res/vclausify_rel
% 3.40/1.00  --clausifier_options                    --mode clausify
% 3.40/1.00  --stdin                                 false
% 3.40/1.00  --stats_out                             all
% 3.40/1.00  
% 3.40/1.00  ------ General Options
% 3.40/1.00  
% 3.40/1.00  --fof                                   false
% 3.40/1.00  --time_out_real                         305.
% 3.40/1.00  --time_out_virtual                      -1.
% 3.40/1.00  --symbol_type_check                     false
% 3.40/1.00  --clausify_out                          false
% 3.40/1.00  --sig_cnt_out                           false
% 3.40/1.00  --trig_cnt_out                          false
% 3.40/1.00  --trig_cnt_out_tolerance                1.
% 3.40/1.00  --trig_cnt_out_sk_spl                   false
% 3.40/1.00  --abstr_cl_out                          false
% 3.40/1.00  
% 3.40/1.00  ------ Global Options
% 3.40/1.00  
% 3.40/1.00  --schedule                              default
% 3.40/1.00  --add_important_lit                     false
% 3.40/1.00  --prop_solver_per_cl                    1000
% 3.40/1.00  --min_unsat_core                        false
% 3.40/1.00  --soft_assumptions                      false
% 3.40/1.00  --soft_lemma_size                       3
% 3.40/1.00  --prop_impl_unit_size                   0
% 3.40/1.00  --prop_impl_unit                        []
% 3.40/1.00  --share_sel_clauses                     true
% 3.40/1.00  --reset_solvers                         false
% 3.40/1.00  --bc_imp_inh                            [conj_cone]
% 3.40/1.00  --conj_cone_tolerance                   3.
% 3.40/1.00  --extra_neg_conj                        none
% 3.40/1.00  --large_theory_mode                     true
% 3.40/1.00  --prolific_symb_bound                   200
% 3.40/1.00  --lt_threshold                          2000
% 3.40/1.00  --clause_weak_htbl                      true
% 3.40/1.00  --gc_record_bc_elim                     false
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing Options
% 3.40/1.00  
% 3.40/1.00  --preprocessing_flag                    true
% 3.40/1.00  --time_out_prep_mult                    0.1
% 3.40/1.00  --splitting_mode                        input
% 3.40/1.00  --splitting_grd                         true
% 3.40/1.00  --splitting_cvd                         false
% 3.40/1.00  --splitting_cvd_svl                     false
% 3.40/1.00  --splitting_nvd                         32
% 3.40/1.00  --sub_typing                            true
% 3.40/1.00  --prep_gs_sim                           true
% 3.40/1.00  --prep_unflatten                        true
% 3.40/1.00  --prep_res_sim                          true
% 3.40/1.00  --prep_upred                            true
% 3.40/1.00  --prep_sem_filter                       exhaustive
% 3.40/1.00  --prep_sem_filter_out                   false
% 3.40/1.00  --pred_elim                             true
% 3.40/1.00  --res_sim_input                         true
% 3.40/1.00  --eq_ax_congr_red                       true
% 3.40/1.00  --pure_diseq_elim                       true
% 3.40/1.00  --brand_transform                       false
% 3.40/1.00  --non_eq_to_eq                          false
% 3.40/1.00  --prep_def_merge                        true
% 3.40/1.00  --prep_def_merge_prop_impl              false
% 3.40/1.00  --prep_def_merge_mbd                    true
% 3.40/1.00  --prep_def_merge_tr_red                 false
% 3.40/1.00  --prep_def_merge_tr_cl                  false
% 3.40/1.00  --smt_preprocessing                     true
% 3.40/1.00  --smt_ac_axioms                         fast
% 3.40/1.00  --preprocessed_out                      false
% 3.40/1.00  --preprocessed_stats                    false
% 3.40/1.00  
% 3.40/1.00  ------ Abstraction refinement Options
% 3.40/1.00  
% 3.40/1.00  --abstr_ref                             []
% 3.40/1.00  --abstr_ref_prep                        false
% 3.40/1.00  --abstr_ref_until_sat                   false
% 3.40/1.00  --abstr_ref_sig_restrict                funpre
% 3.40/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.00  --abstr_ref_under                       []
% 3.40/1.00  
% 3.40/1.00  ------ SAT Options
% 3.40/1.00  
% 3.40/1.00  --sat_mode                              false
% 3.40/1.00  --sat_fm_restart_options                ""
% 3.40/1.00  --sat_gr_def                            false
% 3.40/1.00  --sat_epr_types                         true
% 3.40/1.00  --sat_non_cyclic_types                  false
% 3.40/1.00  --sat_finite_models                     false
% 3.40/1.00  --sat_fm_lemmas                         false
% 3.40/1.00  --sat_fm_prep                           false
% 3.40/1.00  --sat_fm_uc_incr                        true
% 3.40/1.00  --sat_out_model                         small
% 3.40/1.00  --sat_out_clauses                       false
% 3.40/1.00  
% 3.40/1.00  ------ QBF Options
% 3.40/1.00  
% 3.40/1.00  --qbf_mode                              false
% 3.40/1.00  --qbf_elim_univ                         false
% 3.40/1.00  --qbf_dom_inst                          none
% 3.40/1.00  --qbf_dom_pre_inst                      false
% 3.40/1.00  --qbf_sk_in                             false
% 3.40/1.00  --qbf_pred_elim                         true
% 3.40/1.00  --qbf_split                             512
% 3.40/1.00  
% 3.40/1.00  ------ BMC1 Options
% 3.40/1.00  
% 3.40/1.00  --bmc1_incremental                      false
% 3.40/1.00  --bmc1_axioms                           reachable_all
% 3.40/1.00  --bmc1_min_bound                        0
% 3.40/1.00  --bmc1_max_bound                        -1
% 3.40/1.00  --bmc1_max_bound_default                -1
% 3.40/1.00  --bmc1_symbol_reachability              true
% 3.40/1.00  --bmc1_property_lemmas                  false
% 3.40/1.00  --bmc1_k_induction                      false
% 3.40/1.00  --bmc1_non_equiv_states                 false
% 3.40/1.00  --bmc1_deadlock                         false
% 3.40/1.00  --bmc1_ucm                              false
% 3.40/1.00  --bmc1_add_unsat_core                   none
% 3.40/1.00  --bmc1_unsat_core_children              false
% 3.40/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.00  --bmc1_out_stat                         full
% 3.40/1.00  --bmc1_ground_init                      false
% 3.40/1.00  --bmc1_pre_inst_next_state              false
% 3.40/1.00  --bmc1_pre_inst_state                   false
% 3.40/1.00  --bmc1_pre_inst_reach_state             false
% 3.40/1.00  --bmc1_out_unsat_core                   false
% 3.40/1.00  --bmc1_aig_witness_out                  false
% 3.40/1.00  --bmc1_verbose                          false
% 3.40/1.00  --bmc1_dump_clauses_tptp                false
% 3.40/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.00  --bmc1_dump_file                        -
% 3.40/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.00  --bmc1_ucm_extend_mode                  1
% 3.40/1.00  --bmc1_ucm_init_mode                    2
% 3.40/1.00  --bmc1_ucm_cone_mode                    none
% 3.40/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.00  --bmc1_ucm_relax_model                  4
% 3.40/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.00  --bmc1_ucm_layered_model                none
% 3.40/1.00  --bmc1_ucm_max_lemma_size               10
% 3.40/1.00  
% 3.40/1.00  ------ AIG Options
% 3.40/1.00  
% 3.40/1.00  --aig_mode                              false
% 3.40/1.00  
% 3.40/1.00  ------ Instantiation Options
% 3.40/1.00  
% 3.40/1.00  --instantiation_flag                    true
% 3.40/1.00  --inst_sos_flag                         false
% 3.40/1.00  --inst_sos_phase                        true
% 3.40/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel_side                     none
% 3.40/1.00  --inst_solver_per_active                1400
% 3.40/1.00  --inst_solver_calls_frac                1.
% 3.40/1.00  --inst_passive_queue_type               priority_queues
% 3.40/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.00  --inst_passive_queues_freq              [25;2]
% 3.40/1.00  --inst_dismatching                      true
% 3.40/1.00  --inst_eager_unprocessed_to_passive     true
% 3.40/1.00  --inst_prop_sim_given                   true
% 3.40/1.00  --inst_prop_sim_new                     false
% 3.40/1.00  --inst_subs_new                         false
% 3.40/1.00  --inst_eq_res_simp                      false
% 3.40/1.00  --inst_subs_given                       false
% 3.40/1.00  --inst_orphan_elimination               true
% 3.40/1.00  --inst_learning_loop_flag               true
% 3.40/1.00  --inst_learning_start                   3000
% 3.40/1.00  --inst_learning_factor                  2
% 3.40/1.00  --inst_start_prop_sim_after_learn       3
% 3.40/1.00  --inst_sel_renew                        solver
% 3.40/1.00  --inst_lit_activity_flag                true
% 3.40/1.00  --inst_restr_to_given                   false
% 3.40/1.00  --inst_activity_threshold               500
% 3.40/1.00  --inst_out_proof                        true
% 3.40/1.00  
% 3.40/1.00  ------ Resolution Options
% 3.40/1.00  
% 3.40/1.00  --resolution_flag                       false
% 3.40/1.00  --res_lit_sel                           adaptive
% 3.40/1.00  --res_lit_sel_side                      none
% 3.40/1.00  --res_ordering                          kbo
% 3.40/1.00  --res_to_prop_solver                    active
% 3.40/1.00  --res_prop_simpl_new                    false
% 3.40/1.00  --res_prop_simpl_given                  true
% 3.40/1.00  --res_passive_queue_type                priority_queues
% 3.40/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.00  --res_passive_queues_freq               [15;5]
% 3.40/1.00  --res_forward_subs                      full
% 3.40/1.00  --res_backward_subs                     full
% 3.40/1.00  --res_forward_subs_resolution           true
% 3.40/1.00  --res_backward_subs_resolution          true
% 3.40/1.00  --res_orphan_elimination                true
% 3.40/1.00  --res_time_limit                        2.
% 3.40/1.00  --res_out_proof                         true
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Options
% 3.40/1.00  
% 3.40/1.00  --superposition_flag                    true
% 3.40/1.00  --sup_passive_queue_type                priority_queues
% 3.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.40/1.00  --demod_completeness_check              fast
% 3.40/1.00  --demod_use_ground                      true
% 3.40/1.00  --sup_to_prop_solver                    passive
% 3.40/1.00  --sup_prop_simpl_new                    true
% 3.40/1.00  --sup_prop_simpl_given                  true
% 3.40/1.00  --sup_fun_splitting                     false
% 3.40/1.00  --sup_smt_interval                      50000
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Simplification Setup
% 3.40/1.00  
% 3.40/1.00  --sup_indices_passive                   []
% 3.40/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_full_bw                           [BwDemod]
% 3.40/1.00  --sup_immed_triv                        [TrivRules]
% 3.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_immed_bw_main                     []
% 3.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.00  
% 3.40/1.00  ------ Combination Options
% 3.40/1.00  
% 3.40/1.00  --comb_res_mult                         3
% 3.40/1.00  --comb_sup_mult                         2
% 3.40/1.00  --comb_inst_mult                        10
% 3.40/1.00  
% 3.40/1.00  ------ Debug Options
% 3.40/1.00  
% 3.40/1.00  --dbg_backtrace                         false
% 3.40/1.00  --dbg_dump_prop_clauses                 false
% 3.40/1.00  --dbg_dump_prop_clauses_file            -
% 3.40/1.00  --dbg_out_stat                          false
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  ------ Proving...
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  % SZS status Theorem for theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  fof(f7,axiom,(
% 3.40/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f18,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 3.40/1.00    inference(ennf_transformation,[],[f7])).
% 3.40/1.00  
% 3.40/1.00  fof(f31,plain,(
% 3.40/1.00    ! [X6,X5,X4,X3,X2,X1,X0,X7] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 3.40/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.40/1.00  
% 3.40/1.00  fof(f32,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7))),
% 3.40/1.00    inference(definition_folding,[],[f18,f31])).
% 3.40/1.00  
% 3.40/1.00  fof(f38,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)) & (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 3.40/1.00    inference(nnf_transformation,[],[f32])).
% 3.40/1.00  
% 3.40/1.00  fof(f68,plain,(
% 3.40/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 3.40/1.00    inference(cnf_transformation,[],[f38])).
% 3.40/1.00  
% 3.40/1.00  fof(f106,plain,(
% 3.40/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 3.40/1.00    inference(equality_resolution,[],[f68])).
% 3.40/1.00  
% 3.40/1.00  fof(f33,plain,(
% 3.40/1.00    ! [X6,X5,X4,X3,X2,X1,X0,X7] : ((sP0(X6,X5,X4,X3,X2,X1,X0,X7) | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~r2_hidden(X8,X7))) | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)))),
% 3.40/1.00    inference(nnf_transformation,[],[f31])).
% 3.40/1.00  
% 3.40/1.00  fof(f34,plain,(
% 3.40/1.00    ! [X6,X5,X4,X3,X2,X1,X0,X7] : ((sP0(X6,X5,X4,X3,X2,X1,X0,X7) | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X7))) | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)))),
% 3.40/1.00    inference(flattening,[],[f33])).
% 3.40/1.00  
% 3.40/1.00  fof(f35,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : (((X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8 & X6 != X8) | ~r2_hidden(X8,X7)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | X6 = X8 | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 3.40/1.00    inference(rectify,[],[f34])).
% 3.40/1.00  
% 3.40/1.00  fof(f36,plain,(
% 3.40/1.00    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : (((X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8 & X6 != X8) | ~r2_hidden(X8,X7)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | X6 = X8 | r2_hidden(X8,X7))) => (((sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f37,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | (((sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.40/1.00  
% 3.40/1.00  fof(f59,plain,(
% 3.40/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | X0 != X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f37])).
% 3.40/1.00  
% 3.40/1.00  fof(f99,plain,(
% 3.40/1.00    ( ! [X6,X4,X2,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | ~sP0(X9,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.40/1.00    inference(equality_resolution,[],[f59])).
% 3.40/1.00  
% 3.40/1.00  fof(f15,conjecture,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f16,negated_conjecture,(
% 3.40/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 3.40/1.00    inference(negated_conjecture,[],[f15])).
% 3.40/1.00  
% 3.40/1.00  fof(f17,plain,(
% 3.40/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 3.40/1.00    inference(rectify,[],[f16])).
% 3.40/1.00  
% 3.40/1.00  fof(f29,plain,(
% 3.40/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f17])).
% 3.40/1.00  
% 3.40/1.00  fof(f30,plain,(
% 3.40/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f29])).
% 3.40/1.00  
% 3.40/1.00  fof(f44,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) => ((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(X0,X1,X2))))) )),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f43,plain,(
% 3.40/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,sK4)))) & ~r1_tsep_1(X1,sK4) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f42,plain,(
% 3.40/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,sK3,X2)))) & ~r1_tsep_1(sK3,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f41,plain,(
% 3.40/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f45,plain,(
% 3.40/1.00    ((((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) & ~r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f44,f43,f42,f41])).
% 3.40/1.00  
% 3.40/1.00  fof(f85,plain,(
% 3.40/1.00    m1_pre_topc(sK3,sK2)),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f13,axiom,(
% 3.40/1.00    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f25,plain,(
% 3.40/1.00    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f13])).
% 3.40/1.00  
% 3.40/1.00  fof(f26,plain,(
% 3.40/1.00    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f25])).
% 3.40/1.00  
% 3.40/1.00  fof(f78,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f26])).
% 3.40/1.00  
% 3.40/1.00  fof(f12,axiom,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)))))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f23,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f12])).
% 3.40/1.00  
% 3.40/1.00  fof(f24,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f23])).
% 3.40/1.00  
% 3.40/1.00  fof(f39,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(nnf_transformation,[],[f24])).
% 3.40/1.00  
% 3.40/1.00  fof(f74,plain,(
% 3.40/1.00    ( ! [X2,X0,X3,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f39])).
% 3.40/1.00  
% 3.40/1.00  fof(f8,axiom,(
% 3.40/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f70,plain,(
% 3.40/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.40/1.00    inference(cnf_transformation,[],[f8])).
% 3.40/1.00  
% 3.40/1.00  fof(f2,axiom,(
% 3.40/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f47,plain,(
% 3.40/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f2])).
% 3.40/1.00  
% 3.40/1.00  fof(f3,axiom,(
% 3.40/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f48,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f3])).
% 3.40/1.00  
% 3.40/1.00  fof(f4,axiom,(
% 3.40/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f49,plain,(
% 3.40/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f4])).
% 3.40/1.00  
% 3.40/1.00  fof(f5,axiom,(
% 3.40/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f50,plain,(
% 3.40/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f5])).
% 3.40/1.00  
% 3.40/1.00  fof(f6,axiom,(
% 3.40/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f51,plain,(
% 3.40/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f6])).
% 3.40/1.00  
% 3.40/1.00  fof(f91,plain,(
% 3.40/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f50,f51])).
% 3.40/1.00  
% 3.40/1.00  fof(f92,plain,(
% 3.40/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f49,f91])).
% 3.40/1.00  
% 3.40/1.00  fof(f93,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f48,f92])).
% 3.40/1.00  
% 3.40/1.00  fof(f94,plain,(
% 3.40/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f47,f93])).
% 3.40/1.00  
% 3.40/1.00  fof(f95,plain,(
% 3.40/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.40/1.00    inference(definition_unfolding,[],[f70,f94])).
% 3.40/1.00  
% 3.40/1.00  fof(f98,plain,(
% 3.40/1.00    ( ! [X2,X0,X3,X1] : (k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f74,f95])).
% 3.40/1.00  
% 3.40/1.00  fof(f107,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(equality_resolution,[],[f98])).
% 3.40/1.00  
% 3.40/1.00  fof(f88,plain,(
% 3.40/1.00    ~r1_tsep_1(sK3,sK4)),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f84,plain,(
% 3.40/1.00    ~v2_struct_0(sK3)),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f86,plain,(
% 3.40/1.00    ~v2_struct_0(sK4)),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f76,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f26])).
% 3.40/1.00  
% 3.40/1.00  fof(f77,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f26])).
% 3.40/1.00  
% 3.40/1.00  fof(f81,plain,(
% 3.40/1.00    ~v2_struct_0(sK2)),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f83,plain,(
% 3.40/1.00    l1_pre_topc(sK2)),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f87,plain,(
% 3.40/1.00    m1_pre_topc(sK4,sK2)),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f9,axiom,(
% 3.40/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f19,plain,(
% 3.40/1.00    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 3.40/1.00    inference(ennf_transformation,[],[f9])).
% 3.40/1.00  
% 3.40/1.00  fof(f71,plain,(
% 3.40/1.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f19])).
% 3.40/1.00  
% 3.40/1.00  fof(f14,axiom,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f27,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f14])).
% 3.40/1.00  
% 3.40/1.00  fof(f28,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.40/1.00    inference(flattening,[],[f27])).
% 3.40/1.00  
% 3.40/1.00  fof(f40,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.40/1.00    inference(nnf_transformation,[],[f28])).
% 3.40/1.00  
% 3.40/1.00  fof(f79,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f40])).
% 3.40/1.00  
% 3.40/1.00  fof(f82,plain,(
% 3.40/1.00    v2_pre_topc(sK2)),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f1,axiom,(
% 3.40/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f46,plain,(
% 3.40/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f1])).
% 3.40/1.00  
% 3.40/1.00  fof(f96,plain,(
% 3.40/1.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f46,f95])).
% 3.40/1.00  
% 3.40/1.00  fof(f11,axiom,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f21,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f11])).
% 3.40/1.00  
% 3.40/1.00  fof(f22,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f21])).
% 3.40/1.00  
% 3.40/1.00  fof(f73,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f22])).
% 3.40/1.00  
% 3.40/1.00  fof(f10,axiom,(
% 3.40/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f20,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.40/1.00    inference(ennf_transformation,[],[f10])).
% 3.40/1.00  
% 3.40/1.00  fof(f72,plain,(
% 3.40/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f20])).
% 3.40/1.00  
% 3.40/1.00  fof(f90,plain,(
% 3.40/1.00    ( ! [X4,X5] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  fof(f108,plain,(
% 3.40/1.00    ( ! [X5] : (~m1_subset_1(sK5,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 3.40/1.00    inference(equality_resolution,[],[f90])).
% 3.40/1.00  
% 3.40/1.00  fof(f109,plain,(
% 3.40/1.00    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.40/1.00    inference(equality_resolution,[],[f108])).
% 3.40/1.00  
% 3.40/1.00  fof(f89,plain,(
% 3.40/1.00    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))),
% 3.40/1.00    inference(cnf_transformation,[],[f45])).
% 3.40/1.00  
% 3.40/1.00  cnf(c_18,plain,
% 3.40/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X6,X5,X4,X3,X2,X1,X0)) ),
% 3.40/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_7496,plain,
% 3.40/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X6,X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_9,plain,
% 3.40/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) | r2_hidden(X0,X7) ),
% 3.40/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_7505,plain,
% 3.40/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7) != iProver_top
% 3.40/1.00      | r2_hidden(X0,X7) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_10229,plain,
% 3.40/1.00      ( r2_hidden(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X0)) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_7496,c_7505]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_34,negated_conjecture,
% 3.40/1.00      ( m1_pre_topc(sK3,sK2) ),
% 3.40/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_7485,plain,
% 3.40/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_24,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ m1_pre_topc(X2,X1)
% 3.40/1.00      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(X2)
% 3.40/1.00      | ~ l1_pre_topc(X1) ),
% 3.40/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_7492,plain,
% 3.40/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.40/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.40/1.00      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1) = iProver_top
% 3.40/1.00      | v2_struct_0(X1) = iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | v2_struct_0(X2) = iProver_top
% 3.40/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_23,plain,
% 3.40/1.00      ( r1_tsep_1(X0,X1)
% 3.40/1.00      | ~ m1_pre_topc(X0,X2)
% 3.40/1.00      | ~ m1_pre_topc(X1,X2)
% 3.40/1.00      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 3.40/1.00      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 3.40/1.00      | v2_struct_0(X2)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 3.40/1.00      | ~ l1_pre_topc(X2)
% 3.40/1.00      | k1_setfam_1(k5_enumset1(u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1))) = u1_struct_0(k2_tsep_1(X2,X0,X1)) ),
% 3.40/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_31,negated_conjecture,
% 3.40/1.00      ( ~ r1_tsep_1(sK3,sK4) ),
% 3.40/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_505,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ m1_pre_topc(X2,X1)
% 3.40/1.00      | ~ m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 3.40/1.00      | ~ v1_pre_topc(k2_tsep_1(X1,X2,X0))
% 3.40/1.00      | v2_struct_0(X2)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v2_struct_0(k2_tsep_1(X1,X2,X0))
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | k1_setfam_1(k5_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0))) = u1_struct_0(k2_tsep_1(X1,X2,X0))
% 3.40/1.00      | sK3 != X2
% 3.40/1.00      | sK4 != X0 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_506,plain,
% 3.40/1.00      ( ~ m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0)
% 3.40/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.40/1.00      | ~ m1_pre_topc(sK4,X0)
% 3.40/1.00      | ~ v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | v2_struct_0(sK4)
% 3.40/1.01      | ~ l1_pre_topc(X0)
% 3.40/1.01      | k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4)) ),
% 3.40/1.01      inference(unflattening,[status(thm)],[c_505]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_35,negated_conjecture,
% 3.40/1.01      ( ~ v2_struct_0(sK3) ),
% 3.40/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_33,negated_conjecture,
% 3.40/1.01      ( ~ v2_struct_0(sK4) ),
% 3.40/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_510,plain,
% 3.40/1.01      ( ~ m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0)
% 3.40/1.01      | ~ m1_pre_topc(sK3,X0)
% 3.40/1.01      | ~ m1_pre_topc(sK4,X0)
% 3.40/1.01      | ~ v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | ~ l1_pre_topc(X0)
% 3.40/1.01      | k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4)) ),
% 3.40/1.01      inference(global_propositional_subsumption,
% 3.40/1.01                [status(thm)],
% 3.40/1.01                [c_506,c_35,c_33]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7479,plain,
% 3.40/1.01      ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | m1_pre_topc(k2_tsep_1(X0,sK3,sK4),X0) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK3,X0) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,X0) != iProver_top
% 3.40/1.01      | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) != iProver_top
% 3.40/1.01      | v2_struct_0(X0) = iProver_top
% 3.40/1.01      | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) = iProver_top
% 3.40/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_11289,plain,
% 3.40/1.01      ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | m1_pre_topc(sK3,X0) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,X0) != iProver_top
% 3.40/1.01      | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) != iProver_top
% 3.40/1.01      | v2_struct_0(X0) = iProver_top
% 3.40/1.01      | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) = iProver_top
% 3.40/1.01      | v2_struct_0(sK3) = iProver_top
% 3.40/1.01      | v2_struct_0(sK4) = iProver_top
% 3.40/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_7492,c_7479]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_42,plain,
% 3.40/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_44,plain,
% 3.40/1.01      ( v2_struct_0(sK4) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_26,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.01      | ~ m1_pre_topc(X2,X1)
% 3.40/1.01      | v2_struct_0(X1)
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | v2_struct_0(X2)
% 3.40/1.01      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 3.40/1.01      | ~ l1_pre_topc(X1) ),
% 3.40/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8009,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.01      | ~ m1_pre_topc(sK3,X1)
% 3.40/1.01      | v2_struct_0(X1)
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | ~ v2_struct_0(k2_tsep_1(X1,sK3,X0))
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | ~ l1_pre_topc(X1) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_26]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8468,plain,
% 3.40/1.01      ( ~ m1_pre_topc(sK3,X0)
% 3.40/1.01      | ~ m1_pre_topc(sK4,X0)
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | ~ v2_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | v2_struct_0(sK4)
% 3.40/1.01      | ~ l1_pre_topc(X0) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_8009]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8469,plain,
% 3.40/1.01      ( m1_pre_topc(sK3,X0) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,X0) != iProver_top
% 3.40/1.01      | v2_struct_0(X0) = iProver_top
% 3.40/1.01      | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) != iProver_top
% 3.40/1.01      | v2_struct_0(sK3) = iProver_top
% 3.40/1.01      | v2_struct_0(sK4) = iProver_top
% 3.40/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_8468]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_25,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.01      | ~ m1_pre_topc(X2,X1)
% 3.40/1.01      | v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 3.40/1.01      | v2_struct_0(X1)
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | v2_struct_0(X2)
% 3.40/1.01      | ~ l1_pre_topc(X1) ),
% 3.40/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8010,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.01      | ~ m1_pre_topc(sK3,X1)
% 3.40/1.01      | v1_pre_topc(k2_tsep_1(X1,sK3,X0))
% 3.40/1.01      | v2_struct_0(X1)
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | ~ l1_pre_topc(X1) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8478,plain,
% 3.40/1.01      ( ~ m1_pre_topc(sK3,X0)
% 3.40/1.01      | ~ m1_pre_topc(sK4,X0)
% 3.40/1.01      | v1_pre_topc(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | v2_struct_0(sK4)
% 3.40/1.01      | ~ l1_pre_topc(X0) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_8010]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8479,plain,
% 3.40/1.01      ( m1_pre_topc(sK3,X0) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,X0) != iProver_top
% 3.40/1.01      | v1_pre_topc(k2_tsep_1(X0,sK3,sK4)) = iProver_top
% 3.40/1.01      | v2_struct_0(X0) = iProver_top
% 3.40/1.01      | v2_struct_0(sK3) = iProver_top
% 3.40/1.01      | v2_struct_0(sK4) = iProver_top
% 3.40/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_8478]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12382,plain,
% 3.40/1.01      ( v2_struct_0(X0) = iProver_top
% 3.40/1.01      | k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | m1_pre_topc(sK3,X0) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,X0) != iProver_top
% 3.40/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.40/1.01      inference(global_propositional_subsumption,
% 3.40/1.01                [status(thm)],
% 3.40/1.01                [c_11289,c_42,c_44,c_8469,c_8479]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12383,plain,
% 3.40/1.01      ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(X0,sK3,sK4))
% 3.40/1.01      | m1_pre_topc(sK3,X0) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,X0) != iProver_top
% 3.40/1.01      | v2_struct_0(X0) = iProver_top
% 3.40/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.40/1.01      inference(renaming,[status(thm)],[c_12382]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12393,plain,
% 3.40/1.01      ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.40/1.01      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.40/1.01      | v2_struct_0(sK2) = iProver_top
% 3.40/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_7485,c_12383]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_38,negated_conjecture,
% 3.40/1.01      ( ~ v2_struct_0(sK2) ),
% 3.40/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_36,negated_conjecture,
% 3.40/1.01      ( l1_pre_topc(sK2) ),
% 3.40/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_32,negated_conjecture,
% 3.40/1.01      ( m1_pre_topc(sK4,sK2) ),
% 3.40/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_513,plain,
% 3.40/1.01      ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK3,sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK4,sK2)
% 3.40/1.01      | ~ v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
% 3.40/1.01      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.40/1.01      | v2_struct_0(sK2)
% 3.40/1.01      | ~ l1_pre_topc(sK2)
% 3.40/1.01      | k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_510]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7893,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK3,sK2)
% 3.40/1.01      | v1_pre_topc(k2_tsep_1(sK2,sK3,X0))
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | v2_struct_0(sK2)
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | ~ l1_pre_topc(sK2) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8066,plain,
% 3.40/1.01      ( ~ m1_pre_topc(sK3,sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK4,sK2)
% 3.40/1.01      | v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
% 3.40/1.01      | v2_struct_0(sK2)
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | v2_struct_0(sK4)
% 3.40/1.01      | ~ l1_pre_topc(sK2) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_7893]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7907,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK3,sK2)
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | ~ v2_struct_0(k2_tsep_1(sK2,sK3,X0))
% 3.40/1.01      | v2_struct_0(sK2)
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | ~ l1_pre_topc(sK2) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_26]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8082,plain,
% 3.40/1.01      ( ~ m1_pre_topc(sK3,sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK4,sK2)
% 3.40/1.01      | ~ v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.40/1.01      | v2_struct_0(sK2)
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | v2_struct_0(sK4)
% 3.40/1.01      | ~ l1_pre_topc(sK2) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_7907]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7917,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,sK2)
% 3.40/1.01      | m1_pre_topc(k2_tsep_1(sK2,sK3,X0),sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK3,sK2)
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | v2_struct_0(sK2)
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | ~ l1_pre_topc(sK2) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_24]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8298,plain,
% 3.40/1.01      ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK3,sK2)
% 3.40/1.01      | ~ m1_pre_topc(sK4,sK2)
% 3.40/1.01      | v2_struct_0(sK2)
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | v2_struct_0(sK4)
% 3.40/1.01      | ~ l1_pre_topc(sK2) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_7917]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12396,plain,
% 3.40/1.01      ( k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) = u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
% 3.40/1.01      inference(global_propositional_subsumption,
% 3.40/1.01                [status(thm)],
% 3.40/1.01                [c_12393,c_38,c_36,c_35,c_34,c_33,c_32,c_513,c_8066,
% 3.40/1.01                 c_8082,c_8298]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_19,plain,
% 3.40/1.01      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 3.40/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7495,plain,
% 3.40/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.40/1.01      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12453,plain,
% 3.40/1.01      ( r2_hidden(X0,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) != iProver_top
% 3.40/1.01      | r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X0) = iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_12396,c_7495]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12556,plain,
% 3.40/1.01      ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK4)) = iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_10229,c_12453]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_28,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.01      | ~ m1_pre_topc(X2,X1)
% 3.40/1.01      | m1_pre_topc(X0,X2)
% 3.40/1.01      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.40/1.01      | ~ v2_pre_topc(X1)
% 3.40/1.01      | ~ l1_pre_topc(X1) ),
% 3.40/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_37,negated_conjecture,
% 3.40/1.01      ( v2_pre_topc(sK2) ),
% 3.40/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_406,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.01      | ~ m1_pre_topc(X2,X1)
% 3.40/1.01      | m1_pre_topc(X0,X2)
% 3.40/1.01      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.40/1.01      | ~ l1_pre_topc(X1)
% 3.40/1.01      | sK2 != X1 ),
% 3.40/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_407,plain,
% 3.40/1.01      ( m1_pre_topc(X0,X1)
% 3.40/1.01      | ~ m1_pre_topc(X1,sK2)
% 3.40/1.01      | ~ m1_pre_topc(X0,sK2)
% 3.40/1.01      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.40/1.01      | ~ l1_pre_topc(sK2) ),
% 3.40/1.01      inference(unflattening,[status(thm)],[c_406]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_409,plain,
% 3.40/1.01      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.40/1.01      | ~ m1_pre_topc(X0,sK2)
% 3.40/1.01      | ~ m1_pre_topc(X1,sK2)
% 3.40/1.01      | m1_pre_topc(X0,X1) ),
% 3.40/1.01      inference(global_propositional_subsumption,
% 3.40/1.01                [status(thm)],
% 3.40/1.01                [c_407,c_36]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_410,plain,
% 3.40/1.01      ( m1_pre_topc(X0,X1)
% 3.40/1.01      | ~ m1_pre_topc(X0,sK2)
% 3.40/1.01      | ~ m1_pre_topc(X1,sK2)
% 3.40/1.01      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 3.40/1.01      inference(renaming,[status(thm)],[c_409]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7481,plain,
% 3.40/1.01      ( m1_pre_topc(X0,X1) = iProver_top
% 3.40/1.01      | m1_pre_topc(X1,sK2) != iProver_top
% 3.40/1.01      | m1_pre_topc(X0,sK2) != iProver_top
% 3.40/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_13040,plain,
% 3.40/1.01      ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
% 3.40/1.01      | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4) = iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,sK2) != iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_12556,c_7481]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_0,plain,
% 3.40/1.01      ( r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 3.40/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7514,plain,
% 3.40/1.01      ( r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12452,plain,
% 3.40/1.01      ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3)) = iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_12396,c_7514]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12499,plain,
% 3.40/1.01      ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) != iProver_top
% 3.40/1.01      | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) = iProver_top
% 3.40/1.01      | m1_pre_topc(sK3,sK2) != iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_12452,c_7481]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_21,plain,
% 3.40/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/1.01      | m1_subset_1(X0,u1_struct_0(X2))
% 3.40/1.01      | ~ m1_pre_topc(X1,X2)
% 3.40/1.01      | v2_struct_0(X2)
% 3.40/1.01      | v2_struct_0(X1)
% 3.40/1.01      | ~ l1_pre_topc(X2) ),
% 3.40/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_11215,plain,
% 3.40/1.01      ( m1_subset_1(sK5,u1_struct_0(X0))
% 3.40/1.01      | ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
% 3.40/1.01      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
% 3.40/1.01      | v2_struct_0(X0)
% 3.40/1.01      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.40/1.01      | ~ l1_pre_topc(X0) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12187,plain,
% 3.40/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
% 3.40/1.01      | m1_subset_1(sK5,u1_struct_0(sK4))
% 3.40/1.01      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4)
% 3.40/1.01      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.40/1.01      | v2_struct_0(sK4)
% 3.40/1.01      | ~ l1_pre_topc(sK4) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_11215]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12190,plain,
% 3.40/1.01      ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) != iProver_top
% 3.40/1.01      | m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top
% 3.40/1.01      | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK4) != iProver_top
% 3.40/1.01      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.40/1.01      | v2_struct_0(sK4) = iProver_top
% 3.40/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_12187]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12181,plain,
% 3.40/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
% 3.40/1.01      | m1_subset_1(sK5,u1_struct_0(sK3))
% 3.40/1.01      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
% 3.40/1.01      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
% 3.40/1.01      | v2_struct_0(sK3)
% 3.40/1.01      | ~ l1_pre_topc(sK3) ),
% 3.40/1.01      inference(instantiation,[status(thm)],[c_11215]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_12182,plain,
% 3.40/1.01      ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) != iProver_top
% 3.40/1.01      | m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top
% 3.40/1.01      | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) != iProver_top
% 3.40/1.01      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) = iProver_top
% 3.40/1.01      | v2_struct_0(sK3) = iProver_top
% 3.40/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_12181]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8299,plain,
% 3.40/1.01      ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) = iProver_top
% 3.40/1.01      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.40/1.01      | v2_struct_0(sK2) = iProver_top
% 3.40/1.01      | v2_struct_0(sK3) = iProver_top
% 3.40/1.01      | v2_struct_0(sK4) = iProver_top
% 3.40/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_8298]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8083,plain,
% 3.40/1.01      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.40/1.01      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.40/1.01      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) != iProver_top
% 3.40/1.01      | v2_struct_0(sK2) = iProver_top
% 3.40/1.01      | v2_struct_0(sK3) = iProver_top
% 3.40/1.01      | v2_struct_0(sK4) = iProver_top
% 3.40/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_8082]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_20,plain,
% 3.40/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.40/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7494,plain,
% 3.40/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.40/1.01      | l1_pre_topc(X1) != iProver_top
% 3.40/1.01      | l1_pre_topc(X0) = iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8047,plain,
% 3.40/1.01      ( l1_pre_topc(sK2) != iProver_top
% 3.40/1.01      | l1_pre_topc(sK3) = iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_7485,c_7494]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_7487,plain,
% 3.40/1.01      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_8046,plain,
% 3.40/1.01      ( l1_pre_topc(sK2) != iProver_top
% 3.40/1.01      | l1_pre_topc(sK4) = iProver_top ),
% 3.40/1.01      inference(superposition,[status(thm)],[c_7487,c_7494]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_29,negated_conjecture,
% 3.40/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.40/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.40/1.01      inference(cnf_transformation,[],[f109]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_48,plain,
% 3.40/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.40/1.01      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_30,negated_conjecture,
% 3.40/1.01      ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
% 3.40/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_47,plain,
% 3.40/1.01      ( m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) = iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_45,plain,
% 3.40/1.01      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_43,plain,
% 3.40/1.01      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_41,plain,
% 3.40/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(c_39,plain,
% 3.40/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 3.40/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.40/1.01  
% 3.40/1.01  cnf(contradiction,plain,
% 3.40/1.01      ( $false ),
% 3.40/1.01      inference(minisat,
% 3.40/1.01                [status(thm)],
% 3.40/1.01                [c_13040,c_12499,c_12190,c_12182,c_8299,c_8083,c_8047,
% 3.40/1.01                 c_8046,c_48,c_47,c_45,c_44,c_43,c_42,c_41,c_39]) ).
% 3.40/1.01  
% 3.40/1.01  
% 3.40/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/1.01  
% 3.40/1.01  ------                               Statistics
% 3.40/1.01  
% 3.40/1.01  ------ General
% 3.40/1.01  
% 3.40/1.01  abstr_ref_over_cycles:                  0
% 3.40/1.01  abstr_ref_under_cycles:                 0
% 3.40/1.01  gc_basic_clause_elim:                   0
% 3.40/1.01  forced_gc_time:                         0
% 3.40/1.01  parsing_time:                           0.022
% 3.40/1.01  unif_index_cands_time:                  0.
% 3.40/1.01  unif_index_add_time:                    0.
% 3.40/1.01  orderings_time:                         0.
% 3.40/1.01  out_proof_time:                         0.01
% 3.40/1.01  total_time:                             0.434
% 3.40/1.01  num_of_symbols:                         47
% 3.40/1.01  num_of_terms:                           7206
% 3.40/1.01  
% 3.40/1.01  ------ Preprocessing
% 3.40/1.01  
% 3.40/1.01  num_of_splits:                          0
% 3.40/1.01  num_of_split_atoms:                     0
% 3.40/1.01  num_of_reused_defs:                     0
% 3.40/1.01  num_eq_ax_congr_red:                    48
% 3.40/1.01  num_of_sem_filtered_clauses:            1
% 3.40/1.01  num_of_subtypes:                        0
% 3.40/1.01  monotx_restored_types:                  0
% 3.40/1.01  sat_num_of_epr_types:                   0
% 3.40/1.01  sat_num_of_non_cyclic_types:            0
% 3.40/1.01  sat_guarded_non_collapsed_types:        0
% 3.40/1.01  num_pure_diseq_elim:                    0
% 3.40/1.01  simp_replaced_by:                       0
% 3.40/1.01  res_preprocessed:                       179
% 3.40/1.01  prep_upred:                             0
% 3.40/1.01  prep_unflattend:                        416
% 3.40/1.01  smt_new_axioms:                         0
% 3.40/1.01  pred_elim_cands:                        8
% 3.40/1.01  pred_elim:                              2
% 3.40/1.01  pred_elim_cl:                           2
% 3.40/1.01  pred_elim_cycles:                       10
% 3.40/1.01  merged_defs:                            0
% 3.40/1.01  merged_defs_ncl:                        0
% 3.40/1.01  bin_hyper_res:                          0
% 3.40/1.01  prep_cycles:                            4
% 3.40/1.01  pred_elim_time:                         0.143
% 3.40/1.01  splitting_time:                         0.
% 3.40/1.01  sem_filter_time:                        0.
% 3.40/1.01  monotx_time:                            0.
% 3.40/1.01  subtype_inf_time:                       0.
% 3.40/1.01  
% 3.40/1.01  ------ Problem properties
% 3.40/1.01  
% 3.40/1.01  clauses:                                37
% 3.40/1.01  conjectures:                            8
% 3.40/1.01  epr:                                    15
% 3.40/1.01  horn:                                   29
% 3.40/1.01  ground:                                 8
% 3.40/1.01  unary:                                  9
% 3.40/1.01  binary:                                 10
% 3.40/1.01  lits:                                   123
% 3.40/1.01  lits_eq:                                25
% 3.40/1.01  fd_pure:                                0
% 3.40/1.01  fd_pseudo:                              0
% 3.40/1.01  fd_cond:                                0
% 3.40/1.01  fd_pseudo_cond:                         3
% 3.40/1.01  ac_symbols:                             0
% 3.40/1.01  
% 3.40/1.01  ------ Propositional Solver
% 3.40/1.01  
% 3.40/1.01  prop_solver_calls:                      28
% 3.40/1.01  prop_fast_solver_calls:                 2802
% 3.40/1.01  smt_solver_calls:                       0
% 3.40/1.01  smt_fast_solver_calls:                  0
% 3.40/1.01  prop_num_of_clauses:                    2964
% 3.40/1.01  prop_preprocess_simplified:             12339
% 3.40/1.01  prop_fo_subsumed:                       39
% 3.40/1.01  prop_solver_time:                       0.
% 3.40/1.01  smt_solver_time:                        0.
% 3.40/1.01  smt_fast_solver_time:                   0.
% 3.40/1.01  prop_fast_solver_time:                  0.
% 3.40/1.01  prop_unsat_core_time:                   0.
% 3.40/1.01  
% 3.40/1.01  ------ QBF
% 3.40/1.01  
% 3.40/1.01  qbf_q_res:                              0
% 3.40/1.01  qbf_num_tautologies:                    0
% 3.40/1.01  qbf_prep_cycles:                        0
% 3.40/1.01  
% 3.40/1.01  ------ BMC1
% 3.40/1.01  
% 3.40/1.01  bmc1_current_bound:                     -1
% 3.40/1.01  bmc1_last_solved_bound:                 -1
% 3.40/1.01  bmc1_unsat_core_size:                   -1
% 3.40/1.01  bmc1_unsat_core_parents_size:           -1
% 3.40/1.01  bmc1_merge_next_fun:                    0
% 3.40/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.40/1.01  
% 3.40/1.01  ------ Instantiation
% 3.40/1.01  
% 3.40/1.01  inst_num_of_clauses:                    952
% 3.40/1.01  inst_num_in_passive:                    550
% 3.40/1.01  inst_num_in_active:                     307
% 3.40/1.01  inst_num_in_unprocessed:                95
% 3.40/1.01  inst_num_of_loops:                      340
% 3.40/1.01  inst_num_of_learning_restarts:          0
% 3.40/1.01  inst_num_moves_active_passive:          32
% 3.40/1.01  inst_lit_activity:                      0
% 3.40/1.01  inst_lit_activity_moves:                1
% 3.40/1.01  inst_num_tautologies:                   0
% 3.40/1.01  inst_num_prop_implied:                  0
% 3.40/1.01  inst_num_existing_simplified:           0
% 3.40/1.01  inst_num_eq_res_simplified:             0
% 3.40/1.01  inst_num_child_elim:                    0
% 3.40/1.01  inst_num_of_dismatching_blockings:      97
% 3.40/1.01  inst_num_of_non_proper_insts:           552
% 3.40/1.01  inst_num_of_duplicates:                 0
% 3.40/1.01  inst_inst_num_from_inst_to_res:         0
% 3.40/1.01  inst_dismatching_checking_time:         0.
% 3.40/1.01  
% 3.40/1.01  ------ Resolution
% 3.40/1.01  
% 3.40/1.01  res_num_of_clauses:                     0
% 3.40/1.01  res_num_in_passive:                     0
% 3.40/1.01  res_num_in_active:                      0
% 3.40/1.01  res_num_of_loops:                       183
% 3.40/1.01  res_forward_subset_subsumed:            12
% 3.40/1.01  res_backward_subset_subsumed:           0
% 3.40/1.01  res_forward_subsumed:                   0
% 3.40/1.01  res_backward_subsumed:                  0
% 3.40/1.01  res_forward_subsumption_resolution:     0
% 3.40/1.01  res_backward_subsumption_resolution:    0
% 3.40/1.01  res_clause_to_clause_subsumption:       5611
% 3.40/1.01  res_orphan_elimination:                 0
% 3.40/1.01  res_tautology_del:                      34
% 3.40/1.01  res_num_eq_res_simplified:              0
% 3.40/1.01  res_num_sel_changes:                    0
% 3.40/1.01  res_moves_from_active_to_pass:          0
% 3.40/1.01  
% 3.40/1.01  ------ Superposition
% 3.40/1.01  
% 3.40/1.01  sup_time_total:                         0.
% 3.40/1.01  sup_time_generating:                    0.
% 3.40/1.01  sup_time_sim_full:                      0.
% 3.40/1.01  sup_time_sim_immed:                     0.
% 3.40/1.01  
% 3.40/1.01  sup_num_of_clauses:                     73
% 3.40/1.01  sup_num_in_active:                      64
% 3.40/1.01  sup_num_in_passive:                     9
% 3.40/1.01  sup_num_of_loops:                       67
% 3.40/1.01  sup_fw_superposition:                   37
% 3.40/1.01  sup_bw_superposition:                   17
% 3.40/1.01  sup_immediate_simplified:               5
% 3.40/1.01  sup_given_eliminated:                   0
% 3.40/1.01  comparisons_done:                       0
% 3.40/1.01  comparisons_avoided:                    0
% 3.40/1.01  
% 3.40/1.01  ------ Simplifications
% 3.40/1.01  
% 3.40/1.01  
% 3.40/1.01  sim_fw_subset_subsumed:                 4
% 3.40/1.01  sim_bw_subset_subsumed:                 1
% 3.40/1.01  sim_fw_subsumed:                        0
% 3.40/1.01  sim_bw_subsumed:                        1
% 3.40/1.01  sim_fw_subsumption_res:                 1
% 3.40/1.01  sim_bw_subsumption_res:                 0
% 3.40/1.01  sim_tautology_del:                      1
% 3.40/1.01  sim_eq_tautology_del:                   5
% 3.40/1.01  sim_eq_res_simp:                        0
% 3.40/1.01  sim_fw_demodulated:                     0
% 3.40/1.01  sim_bw_demodulated:                     3
% 3.40/1.01  sim_light_normalised:                   0
% 3.40/1.01  sim_joinable_taut:                      0
% 3.40/1.01  sim_joinable_simp:                      0
% 3.40/1.01  sim_ac_normalised:                      0
% 3.40/1.01  sim_smt_subsumption:                    0
% 3.40/1.01  
%------------------------------------------------------------------------------

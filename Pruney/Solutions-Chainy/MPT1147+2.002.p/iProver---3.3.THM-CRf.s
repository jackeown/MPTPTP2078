%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:04 EST 2020

% Result     : Theorem 1.41s
% Output     : CNFRefutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  209 (1386 expanded)
%              Number of clauses        :  149 ( 312 expanded)
%              Number of leaves         :   13 ( 388 expanded)
%              Depth                    :   20
%              Number of atoms          : 1096 (14721 expanded)
%              Number of equality atoms :  205 ( 279 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    ! [X2,X1,X0] :
      ( sP1(X2,X1,X0)
    <=> ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ! [X3] :
            ( ~ r2_hidden(X2,X3)
            | ~ r2_hidden(X1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X3,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X2,X3)
            & r2_hidden(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X3,X0) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r2_hidden(X1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
            | ~ v6_orders_2(X3,X2) ) )
      & ( ? [X4] :
            ( r2_hidden(X0,X4)
            & r2_hidden(X1,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & v6_orders_2(X4,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X0,X4)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X4,X2) )
     => ( r2_hidden(X0,sK3(X0,X1,X2))
        & r2_hidden(X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r2_hidden(X1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
            | ~ v6_orders_2(X3,X2) ) )
      & ( ( r2_hidden(X0,sK3(X0,X1,X2))
          & r2_hidden(X1,sK3(X0,X1,X2))
          & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(sK3(X0,X1,X2),X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v6_orders_2(X3,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <=> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                <=> ( r2_orders_2(X0,X1,X2)
                  <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( sP1(X2,X1,X0)
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f13,f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ~ sP1(X2,X1,X0) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | sP1(X2,X1,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ~ sP1(X2,X1,X0) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | sP1(X2,X1,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ( ( r1_orders_2(X0,X2,X1)
                | ~ r2_orders_2(X0,X1,X2) )
              & ( ~ r1_orders_2(X0,X2,X1)
                | r2_orders_2(X0,X1,X2) ) )
            | ~ sP1(X2,X1,X0) )
          & ( ( ( r2_orders_2(X0,X1,X2)
                | r1_orders_2(X0,X2,X1) )
              & ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_orders_2(X0,X1,X2) ) )
            | sP1(X2,X1,X0) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ( ( r1_orders_2(X0,sK6,X1)
              | ~ r2_orders_2(X0,X1,sK6) )
            & ( ~ r1_orders_2(X0,sK6,X1)
              | r2_orders_2(X0,X1,sK6) ) )
          | ~ sP1(sK6,X1,X0) )
        & ( ( ( r2_orders_2(X0,X1,sK6)
              | r1_orders_2(X0,sK6,X1) )
            & ( ~ r1_orders_2(X0,sK6,X1)
              | ~ r2_orders_2(X0,X1,sK6) ) )
          | sP1(sK6,X1,X0) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ~ sP1(X2,X1,X0) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | sP1(X2,X1,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ( ( r1_orders_2(X0,X2,sK5)
                  | ~ r2_orders_2(X0,sK5,X2) )
                & ( ~ r1_orders_2(X0,X2,sK5)
                  | r2_orders_2(X0,sK5,X2) ) )
              | ~ sP1(X2,sK5,X0) )
            & ( ( ( r2_orders_2(X0,sK5,X2)
                  | r1_orders_2(X0,X2,sK5) )
                & ( ~ r1_orders_2(X0,X2,sK5)
                  | ~ r2_orders_2(X0,sK5,X2) ) )
              | sP1(X2,sK5,X0) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ( r1_orders_2(X0,X2,X1)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X1)
                      | r2_orders_2(X0,X1,X2) ) )
                  | ~ sP1(X2,X1,X0) )
                & ( ( ( r2_orders_2(X0,X1,X2)
                      | r1_orders_2(X0,X2,X1) )
                    & ( ~ r1_orders_2(X0,X2,X1)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | sP1(X2,X1,X0) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(sK4,X2,X1)
                    | ~ r2_orders_2(sK4,X1,X2) )
                  & ( ~ r1_orders_2(sK4,X2,X1)
                    | r2_orders_2(sK4,X1,X2) ) )
                | ~ sP1(X2,X1,sK4) )
              & ( ( ( r2_orders_2(sK4,X1,X2)
                    | r1_orders_2(sK4,X2,X1) )
                  & ( ~ r1_orders_2(sK4,X2,X1)
                    | ~ r2_orders_2(sK4,X1,X2) ) )
                | sP1(X2,X1,sK4) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ( ( r1_orders_2(sK4,sK6,sK5)
          | ~ r2_orders_2(sK4,sK5,sK6) )
        & ( ~ r1_orders_2(sK4,sK6,sK5)
          | r2_orders_2(sK4,sK5,sK6) ) )
      | ~ sP1(sK6,sK5,sK4) )
    & ( ( ( r2_orders_2(sK4,sK5,sK6)
          | r1_orders_2(sK4,sK6,sK5) )
        & ( ~ r1_orders_2(sK4,sK6,sK5)
          | ~ r2_orders_2(sK4,sK5,sK6) ) )
      | sP1(sK6,sK5,sK4) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).

fof(f60,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | sP1(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(sK3(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK3(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP0(X2,X1,X0)
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f11,f14])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP0(X2,X1,X0)
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X1)
      | r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ( ~ r1_orders_2(X0,X2,X1)
        & ~ r1_orders_2(X0,X1,X2) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
      | ( ~ r1_orders_2(X2,X0,X1)
        & ~ r1_orders_2(X2,X1,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
     => ( r2_hidden(X0,sK2(X0,X1,X2))
        & r2_hidden(X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK2(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,sK2(X0,X1,X2))
        & r2_hidden(X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK2(X0,X1,X2),X2) )
      | ( ~ r1_orders_2(X2,X0,X1)
        & ~ r1_orders_2(X2,X1,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK2(X0,X1,X2))
      | ~ r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK2(X0,X1,X2))
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(sK2(X0,X1,X2),X2)
      | ~ r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(sK2(X0,X1,X2),X2)
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,
    ( r1_orders_2(sK4,sK6,sK5)
    | ~ r2_orders_2(sK4,sK5,sK6)
    | ~ sP1(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( ~ r1_orders_2(sK4,sK6,sK5)
    | r2_orders_2(sK4,sK5,sK6)
    | ~ sP1(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( sP1(X0,X1,X2)
    | ~ v6_orders_2(X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X0,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2224,plain,
    ( sP1(X0_46,X1_46,X0_45)
    | ~ v6_orders_2(X2_46,X0_45)
    | ~ r2_hidden(X0_46,X2_46)
    | ~ r2_hidden(X1_46,X2_46)
    | ~ m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(X0_45))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2931,plain,
    ( sP1(X0_46,X1_46,sK4)
    | ~ v6_orders_2(sK2(sK6,sK5,sK4),sK4)
    | ~ r2_hidden(X0_46,sK2(sK6,sK5,sK4))
    | ~ r2_hidden(X1_46,sK2(sK6,sK5,sK4))
    | ~ m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_3981,plain,
    ( sP1(sK6,sK5,sK4)
    | ~ v6_orders_2(sK2(sK6,sK5,sK4),sK4)
    | ~ r2_hidden(sK5,sK2(sK6,sK5,sK4))
    | ~ r2_hidden(sK6,sK2(sK6,sK5,sK4))
    | ~ m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2931])).

cnf(c_3982,plain,
    ( sP1(sK6,sK5,sK4) = iProver_top
    | v6_orders_2(sK2(sK6,sK5,sK4),sK4) != iProver_top
    | r2_hidden(sK5,sK2(sK6,sK5,sK4)) != iProver_top
    | r2_hidden(sK6,sK2(sK6,sK5,sK4)) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3981])).

cnf(c_21,negated_conjecture,
    ( sP1(sK6,sK5,sK4)
    | r1_orders_2(sK4,sK6,sK5)
    | r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_395,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_25])).

cnf(c_396,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ r2_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_1162,plain,
    ( sP1(sK6,sK5,sK4)
    | r1_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | sK5 != X0
    | sK6 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_396])).

cnf(c_1163,plain,
    ( sP1(sK6,sK5,sK4)
    | r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1162])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1165,plain,
    ( sP1(sK6,sK5,sK4)
    | r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1163,c_24,c_23])).

cnf(c_2207,plain,
    ( sP1(sK6,sK5,sK4)
    | r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5) ),
    inference(subtyping,[status(esa)],[c_1165])).

cnf(c_2656,plain,
    ( sP1(sK6,sK5,sK4) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2207])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1,X2)
    | r2_hidden(X1,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2222,plain,
    ( ~ sP1(X0_46,X1_46,X0_45)
    | r2_hidden(X1_46,sK3(X0_46,X1_46,X0_45)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2641,plain,
    ( sP1(X0_46,X1_46,X0_45) != iProver_top
    | r2_hidden(X1_46,sK3(X0_46,X1_46,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2222])).

cnf(c_17,plain,
    ( ~ sP1(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2221,plain,
    ( ~ sP1(X0_46,X1_46,X0_45)
    | m1_subset_1(sK3(X0_46,X1_46,X0_45),k1_zfmisc_1(u1_struct_0(X0_45))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2642,plain,
    ( sP1(X0_46,X1_46,X0_45) != iProver_top
    | m1_subset_1(sK3(X0_46,X1_46,X0_45),k1_zfmisc_1(u1_struct_0(X0_45))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2221])).

cnf(c_2639,plain,
    ( sP1(X0_46,X1_46,X0_45) = iProver_top
    | v6_orders_2(X2_46,X0_45) != iProver_top
    | r2_hidden(X1_46,X2_46) != iProver_top
    | r2_hidden(X0_46,X2_46) != iProver_top
    | m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(X0_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2224])).

cnf(c_3076,plain,
    ( sP1(X0_46,X1_46,X0_45) != iProver_top
    | sP1(X2_46,X3_46,X0_45) = iProver_top
    | v6_orders_2(sK3(X0_46,X1_46,X0_45),X0_45) != iProver_top
    | r2_hidden(X3_46,sK3(X0_46,X1_46,X0_45)) != iProver_top
    | r2_hidden(X2_46,sK3(X0_46,X1_46,X0_45)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_2639])).

cnf(c_18,plain,
    ( ~ sP1(X0,X1,X2)
    | v6_orders_2(sK3(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2220,plain,
    ( ~ sP1(X0_46,X1_46,X0_45)
    | v6_orders_2(sK3(X0_46,X1_46,X0_45),X0_45) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2250,plain,
    ( sP1(X0_46,X1_46,X0_45) != iProver_top
    | v6_orders_2(sK3(X0_46,X1_46,X0_45),X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2220])).

cnf(c_3396,plain,
    ( sP1(X2_46,X3_46,X0_45) = iProver_top
    | sP1(X0_46,X1_46,X0_45) != iProver_top
    | r2_hidden(X3_46,sK3(X0_46,X1_46,X0_45)) != iProver_top
    | r2_hidden(X2_46,sK3(X0_46,X1_46,X0_45)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3076,c_2250])).

cnf(c_3397,plain,
    ( sP1(X0_46,X1_46,X0_45) != iProver_top
    | sP1(X2_46,X3_46,X0_45) = iProver_top
    | r2_hidden(X3_46,sK3(X0_46,X1_46,X0_45)) != iProver_top
    | r2_hidden(X2_46,sK3(X0_46,X1_46,X0_45)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3396])).

cnf(c_3404,plain,
    ( sP1(X0_46,X1_46,X0_45) != iProver_top
    | sP1(X2_46,X1_46,X0_45) = iProver_top
    | r2_hidden(X2_46,sK3(X0_46,X1_46,X0_45)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_3397])).

cnf(c_3424,plain,
    ( sP1(X0_46,X1_46,X0_45) != iProver_top
    | sP1(X1_46,X1_46,X0_45) = iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_3404])).

cnf(c_3488,plain,
    ( sP1(sK5,sK5,sK4) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_3424])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1421,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | v6_orders_2(sK3(X0,X1,X2),X2)
    | sK5 != X1
    | sK6 != X0
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1165])).

cnf(c_1422,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | v6_orders_2(sK3(sK6,sK5,sK4),sK4) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_1423,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | v6_orders_2(sK3(sK6,sK5,sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1422])).

cnf(c_1447,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | sK5 != X1
    | sK6 != X0
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1165])).

cnf(c_1448,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_1447])).

cnf(c_1449,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_1473,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | r2_hidden(X0,sK3(X1,X0,X2))
    | sK5 != X0
    | sK6 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_1165])).

cnf(c_1474,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | r2_hidden(sK5,sK3(sK6,sK5,sK4)) ),
    inference(unflattening,[status(thm)],[c_1473])).

cnf(c_1475,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK3(sK6,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2)
    | r2_hidden(X0,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1499,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | r2_hidden(X0,sK3(X0,X1,X2))
    | sK5 != X1
    | sK6 != X0
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_1165])).

cnf(c_1500,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | r2_hidden(sK6,sK3(sK6,sK5,sK4)) ),
    inference(unflattening,[status(thm)],[c_1499])).

cnf(c_1501,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | r2_hidden(sK6,sK3(sK6,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X2,X1)
    | ~ v6_orders_2(X3,X0)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_325,plain,
    ( r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X2,X1)
    | ~ v6_orders_2(X3,X0)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_326,plain,
    ( r1_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X1,X0)
    | ~ v6_orders_2(X2,sK4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v6_orders_2(X2,sK4)
    | r1_orders_2(sK4,X1,X0)
    | r1_orders_2(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_326,c_25])).

cnf(c_331,plain,
    ( r1_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X1,X0)
    | ~ v6_orders_2(X2,sK4)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_330])).

cnf(c_2217,plain,
    ( r1_orders_2(sK4,X0_46,X1_46)
    | r1_orders_2(sK4,X1_46,X0_46)
    | ~ v6_orders_2(X2_46,sK4)
    | ~ r2_hidden(X0_46,X2_46)
    | ~ r2_hidden(X1_46,X2_46)
    | ~ m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_331])).

cnf(c_3030,plain,
    ( r1_orders_2(sK4,X0_46,X1_46)
    | r1_orders_2(sK4,X1_46,X0_46)
    | ~ v6_orders_2(sK3(sK6,sK5,sK4),sK4)
    | ~ r2_hidden(X0_46,sK3(sK6,sK5,sK4))
    | ~ r2_hidden(X1_46,sK3(sK6,sK5,sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_3385,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ v6_orders_2(sK3(sK6,sK5,sK4),sK4)
    | ~ r2_hidden(sK5,sK3(sK6,sK5,sK4))
    | ~ r2_hidden(sK6,sK3(sK6,sK5,sK4))
    | ~ m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_3386,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | v6_orders_2(sK3(sK6,sK5,sK4),sK4) != iProver_top
    | r2_hidden(sK5,sK3(sK6,sK5,sK4)) != iProver_top
    | r2_hidden(sK6,sK3(sK6,sK5,sK4)) != iProver_top
    | m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3385])).

cnf(c_3532,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3488,c_31,c_32,c_1423,c_1449,c_1475,c_1501,c_3386])).

cnf(c_2228,plain,
    ( ~ r1_orders_2(X0_45,X0_46,X1_46)
    | r1_orders_2(X0_45,X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_3349,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | r1_orders_2(sK4,sK6,sK5)
    | sK5 != X1_46
    | sK6 != X0_46 ),
    inference(instantiation,[status(thm)],[c_2228])).

cnf(c_3350,plain,
    ( sK5 != X0_46
    | sK6 != X1_46
    | r1_orders_2(sK4,X1_46,X0_46) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3349])).

cnf(c_3352,plain,
    ( sK5 != sK5
    | sK6 != sK5
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3350])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X1,X0)
    | r2_hidden(X1,sK2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_361,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_362,plain,
    ( sP0(X0,X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | sP0(X0,X1,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_25])).

cnf(c_367,plain,
    ( sP0(X0,X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_528,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,sK2(X2,X1,X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | X4 != X2
    | X3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_367])).

cnf(c_529,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | r2_hidden(X0,sK2(X1,X0,sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_2212,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | r2_hidden(X0_46,sK2(X1_46,X0_46,sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_529])).

cnf(c_3127,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | r2_hidden(sK5,sK2(sK6,sK5,sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2212])).

cnf(c_3149,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r2_hidden(sK5,sK2(sK6,sK5,sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3127])).

cnf(c_5,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X1,X0)
    | r2_hidden(X0,sK2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_562,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X2,sK2(X2,X1,X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | X4 != X2
    | X3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_367])).

cnf(c_563,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | r2_hidden(X1,sK2(X1,X0,sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_2210,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | r2_hidden(X1_46,sK2(X1_46,X0_46,sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_563])).

cnf(c_3129,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | r2_hidden(sK6,sK2(sK6,sK5,sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2210])).

cnf(c_3145,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r2_hidden(sK6,sK2(sK6,sK5,sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3129])).

cnf(c_4,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X0,X1)
    | r2_hidden(X0,sK2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_578,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,sK2(X1,X2,X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | X4 != X1
    | X3 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_367])).

cnf(c_579,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | r2_hidden(X0,sK2(X0,X1,sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_2209,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | r2_hidden(X0_46,sK2(X0_46,X1_46,sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_579])).

cnf(c_3130,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | r2_hidden(sK5,sK2(sK5,sK6,sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_3143,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r2_hidden(sK5,sK2(sK5,sK6,sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3130])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X1,X0)
    | v6_orders_2(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_460,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | v6_orders_2(sK2(X2,X1,X0),X0)
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | X4 != X2
    | X3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_367])).

cnf(c_461,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | v6_orders_2(sK2(X1,X0,sK4),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_2216,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | v6_orders_2(sK2(X1_46,X0_46,sK4),sK4)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_461])).

cnf(c_3131,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | v6_orders_2(sK2(sK6,sK5,sK4),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_3141,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | v6_orders_2(sK2(sK6,sK5,sK4),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3131])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X0,X1)
    | v6_orders_2(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_478,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | v6_orders_2(sK2(X1,X2,X0),X0)
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | X4 != X1
    | X3 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_367])).

cnf(c_479,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | v6_orders_2(sK2(X0,X1,sK4),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_2215,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | v6_orders_2(sK2(X0_46,X1_46,sK4),sK4)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_479])).

cnf(c_3132,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | v6_orders_2(sK2(sK5,sK6,sK4),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_3139,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | v6_orders_2(sK2(sK5,sK6,sK4),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3132])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X1,X0)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_494,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | m1_subset_1(sK2(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X0)))
    | X4 != X2
    | X3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_367])).

cnf(c_495,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(X1,X0,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_2214,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | m1_subset_1(sK2(X1_46,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_3133,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_3137,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3133])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X0,X1)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_512,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X0)))
    | X4 != X1
    | X3 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_367])).

cnf(c_513,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_2213,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | m1_subset_1(sK2(X0_46,X1_46,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_3134,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_3135,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3134])).

cnf(c_2941,plain,
    ( r1_orders_2(sK4,X0_46,X1_46)
    | r1_orders_2(sK4,X1_46,X0_46)
    | ~ v6_orders_2(sK2(sK5,sK6,sK4),sK4)
    | ~ r2_hidden(X0_46,sK2(sK5,sK6,sK4))
    | ~ r2_hidden(X1_46,sK2(sK5,sK6,sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_2942,plain,
    ( r1_orders_2(sK4,X0_46,X1_46) = iProver_top
    | r1_orders_2(sK4,X1_46,X0_46) = iProver_top
    | v6_orders_2(sK2(sK5,sK6,sK4),sK4) != iProver_top
    | r2_hidden(X0_46,sK2(sK5,sK6,sK4)) != iProver_top
    | r2_hidden(X1_46,sK2(sK5,sK6,sK4)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2941])).

cnf(c_2944,plain,
    ( r1_orders_2(sK4,sK5,sK5) = iProver_top
    | v6_orders_2(sK2(sK5,sK6,sK4),sK4) != iProver_top
    | r2_hidden(sK5,sK2(sK5,sK6,sK4)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X0,X1)
    | r2_hidden(X1,sK2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_546,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X2,sK2(X1,X2,X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | X4 != X1
    | X3 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_367])).

cnf(c_547,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | r2_hidden(X1,sK2(X0,X1,sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_2211,plain,
    ( ~ r1_orders_2(sK4,X0_46,X1_46)
    | r2_hidden(X1_46,sK2(X0_46,X1_46,sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_547])).

cnf(c_2880,plain,
    ( ~ r1_orders_2(sK4,sK6,sK5)
    | r2_hidden(sK5,sK2(sK6,sK5,sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_2881,plain,
    ( r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r2_hidden(sK5,sK2(sK6,sK5,sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2880])).

cnf(c_2874,plain,
    ( ~ r1_orders_2(sK4,sK6,sK5)
    | r2_hidden(sK6,sK2(sK6,sK5,sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_2875,plain,
    ( r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r2_hidden(sK6,sK2(sK6,sK5,sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2874])).

cnf(c_2868,plain,
    ( ~ r1_orders_2(sK4,sK6,sK5)
    | v6_orders_2(sK2(sK6,sK5,sK4),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_2869,plain,
    ( r1_orders_2(sK4,sK6,sK5) != iProver_top
    | v6_orders_2(sK2(sK6,sK5,sK4),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2868])).

cnf(c_2858,plain,
    ( ~ r1_orders_2(sK4,sK6,sK5)
    | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_2859,plain,
    ( r1_orders_2(sK4,sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2858])).

cnf(c_19,negated_conjecture,
    ( ~ sP1(sK6,sK5,sK4)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_425,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | X2 = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_426,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | r2_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_1203,plain,
    ( ~ sP1(sK6,sK5,sK4)
    | ~ r1_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | X1 = X0
    | sK5 != X0
    | sK6 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_426])).

cnf(c_1204,plain,
    ( ~ sP1(sK6,sK5,sK4)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | sK6 = sK5 ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_20,negated_conjecture,
    ( ~ sP1(sK6,sK5,sK4)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_296,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_297,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ r2_orders_2(sK4,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_orders_2(sK4,X1,X0)
    | ~ r1_orders_2(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_297,c_25])).

cnf(c_302,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ r2_orders_2(sK4,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_301])).

cnf(c_1148,plain,
    ( ~ sP1(sK6,sK5,sK4)
    | ~ r1_orders_2(sK4,X0,X1)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | sK5 != X1
    | sK6 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_302])).

cnf(c_1149,plain,
    ( ~ sP1(sK6,sK5,sK4)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1148])).

cnf(c_1151,plain,
    ( ~ sP1(sK6,sK5,sK4)
    | ~ r1_orders_2(sK4,sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1149,c_24,c_23])).

cnf(c_1206,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | ~ sP1(sK6,sK5,sK4)
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_24,c_23,c_1149])).

cnf(c_1207,plain,
    ( ~ sP1(sK6,sK5,sK4)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | sK6 = sK5 ),
    inference(renaming,[status(thm)],[c_1206])).

cnf(c_2205,plain,
    ( ~ sP1(sK6,sK5,sK4)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | sK6 = sK5 ),
    inference(subtyping,[status(esa)],[c_1207])).

cnf(c_2275,plain,
    ( sK6 = sK5
    | sP1(sK6,sK5,sK4) != iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2205])).

cnf(c_2226,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_2239,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2226])).

cnf(c_1153,plain,
    ( sP1(sK6,sK5,sK4) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3982,c_3532,c_3352,c_3149,c_3145,c_3143,c_3141,c_3139,c_3137,c_3135,c_2944,c_2881,c_2875,c_2869,c_2859,c_2275,c_2239,c_1153,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:52:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.41/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.41/1.00  
% 1.41/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.41/1.00  
% 1.41/1.00  ------  iProver source info
% 1.41/1.00  
% 1.41/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.41/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.41/1.00  git: non_committed_changes: false
% 1.41/1.00  git: last_make_outside_of_git: false
% 1.41/1.00  
% 1.41/1.00  ------ 
% 1.41/1.00  
% 1.41/1.00  ------ Input Options
% 1.41/1.00  
% 1.41/1.00  --out_options                           all
% 1.41/1.00  --tptp_safe_out                         true
% 1.41/1.00  --problem_path                          ""
% 1.41/1.00  --include_path                          ""
% 1.41/1.00  --clausifier                            res/vclausify_rel
% 1.41/1.00  --clausifier_options                    --mode clausify
% 1.41/1.00  --stdin                                 false
% 1.41/1.00  --stats_out                             all
% 1.41/1.00  
% 1.41/1.00  ------ General Options
% 1.41/1.00  
% 1.41/1.00  --fof                                   false
% 1.41/1.00  --time_out_real                         305.
% 1.41/1.00  --time_out_virtual                      -1.
% 1.41/1.00  --symbol_type_check                     false
% 1.41/1.00  --clausify_out                          false
% 1.41/1.00  --sig_cnt_out                           false
% 1.41/1.00  --trig_cnt_out                          false
% 1.41/1.00  --trig_cnt_out_tolerance                1.
% 1.41/1.00  --trig_cnt_out_sk_spl                   false
% 1.41/1.00  --abstr_cl_out                          false
% 1.41/1.00  
% 1.41/1.00  ------ Global Options
% 1.41/1.00  
% 1.41/1.00  --schedule                              default
% 1.41/1.00  --add_important_lit                     false
% 1.41/1.00  --prop_solver_per_cl                    1000
% 1.41/1.00  --min_unsat_core                        false
% 1.41/1.00  --soft_assumptions                      false
% 1.41/1.00  --soft_lemma_size                       3
% 1.41/1.00  --prop_impl_unit_size                   0
% 1.41/1.00  --prop_impl_unit                        []
% 1.41/1.00  --share_sel_clauses                     true
% 1.41/1.00  --reset_solvers                         false
% 1.41/1.00  --bc_imp_inh                            [conj_cone]
% 1.41/1.00  --conj_cone_tolerance                   3.
% 1.41/1.00  --extra_neg_conj                        none
% 1.41/1.00  --large_theory_mode                     true
% 1.41/1.00  --prolific_symb_bound                   200
% 1.41/1.00  --lt_threshold                          2000
% 1.41/1.00  --clause_weak_htbl                      true
% 1.41/1.00  --gc_record_bc_elim                     false
% 1.41/1.00  
% 1.41/1.00  ------ Preprocessing Options
% 1.41/1.00  
% 1.41/1.00  --preprocessing_flag                    true
% 1.41/1.00  --time_out_prep_mult                    0.1
% 1.41/1.00  --splitting_mode                        input
% 1.41/1.00  --splitting_grd                         true
% 1.41/1.00  --splitting_cvd                         false
% 1.41/1.00  --splitting_cvd_svl                     false
% 1.41/1.00  --splitting_nvd                         32
% 1.41/1.00  --sub_typing                            true
% 1.41/1.00  --prep_gs_sim                           true
% 1.41/1.00  --prep_unflatten                        true
% 1.41/1.00  --prep_res_sim                          true
% 1.41/1.00  --prep_upred                            true
% 1.41/1.00  --prep_sem_filter                       exhaustive
% 1.41/1.00  --prep_sem_filter_out                   false
% 1.41/1.00  --pred_elim                             true
% 1.41/1.00  --res_sim_input                         true
% 1.41/1.00  --eq_ax_congr_red                       true
% 1.41/1.00  --pure_diseq_elim                       true
% 1.41/1.00  --brand_transform                       false
% 1.41/1.00  --non_eq_to_eq                          false
% 1.41/1.00  --prep_def_merge                        true
% 1.41/1.00  --prep_def_merge_prop_impl              false
% 1.41/1.00  --prep_def_merge_mbd                    true
% 1.41/1.00  --prep_def_merge_tr_red                 false
% 1.41/1.00  --prep_def_merge_tr_cl                  false
% 1.41/1.00  --smt_preprocessing                     true
% 1.41/1.00  --smt_ac_axioms                         fast
% 1.41/1.00  --preprocessed_out                      false
% 1.41/1.00  --preprocessed_stats                    false
% 1.41/1.00  
% 1.41/1.00  ------ Abstraction refinement Options
% 1.41/1.00  
% 1.41/1.00  --abstr_ref                             []
% 1.41/1.00  --abstr_ref_prep                        false
% 1.41/1.00  --abstr_ref_until_sat                   false
% 1.41/1.00  --abstr_ref_sig_restrict                funpre
% 1.41/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.41/1.00  --abstr_ref_under                       []
% 1.41/1.00  
% 1.41/1.00  ------ SAT Options
% 1.41/1.00  
% 1.41/1.00  --sat_mode                              false
% 1.41/1.00  --sat_fm_restart_options                ""
% 1.41/1.00  --sat_gr_def                            false
% 1.41/1.00  --sat_epr_types                         true
% 1.41/1.00  --sat_non_cyclic_types                  false
% 1.41/1.00  --sat_finite_models                     false
% 1.41/1.00  --sat_fm_lemmas                         false
% 1.41/1.00  --sat_fm_prep                           false
% 1.41/1.00  --sat_fm_uc_incr                        true
% 1.41/1.00  --sat_out_model                         small
% 1.41/1.00  --sat_out_clauses                       false
% 1.41/1.00  
% 1.41/1.00  ------ QBF Options
% 1.41/1.00  
% 1.41/1.00  --qbf_mode                              false
% 1.41/1.00  --qbf_elim_univ                         false
% 1.41/1.00  --qbf_dom_inst                          none
% 1.41/1.00  --qbf_dom_pre_inst                      false
% 1.41/1.00  --qbf_sk_in                             false
% 1.41/1.00  --qbf_pred_elim                         true
% 1.41/1.00  --qbf_split                             512
% 1.41/1.00  
% 1.41/1.00  ------ BMC1 Options
% 1.41/1.00  
% 1.41/1.00  --bmc1_incremental                      false
% 1.41/1.00  --bmc1_axioms                           reachable_all
% 1.41/1.00  --bmc1_min_bound                        0
% 1.41/1.00  --bmc1_max_bound                        -1
% 1.41/1.00  --bmc1_max_bound_default                -1
% 1.41/1.00  --bmc1_symbol_reachability              true
% 1.41/1.00  --bmc1_property_lemmas                  false
% 1.41/1.00  --bmc1_k_induction                      false
% 1.41/1.00  --bmc1_non_equiv_states                 false
% 1.41/1.00  --bmc1_deadlock                         false
% 1.41/1.00  --bmc1_ucm                              false
% 1.41/1.00  --bmc1_add_unsat_core                   none
% 1.41/1.00  --bmc1_unsat_core_children              false
% 1.41/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.41/1.00  --bmc1_out_stat                         full
% 1.41/1.00  --bmc1_ground_init                      false
% 1.41/1.00  --bmc1_pre_inst_next_state              false
% 1.41/1.00  --bmc1_pre_inst_state                   false
% 1.41/1.00  --bmc1_pre_inst_reach_state             false
% 1.41/1.00  --bmc1_out_unsat_core                   false
% 1.41/1.00  --bmc1_aig_witness_out                  false
% 1.41/1.00  --bmc1_verbose                          false
% 1.41/1.00  --bmc1_dump_clauses_tptp                false
% 1.41/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.41/1.00  --bmc1_dump_file                        -
% 1.41/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.41/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.41/1.00  --bmc1_ucm_extend_mode                  1
% 1.41/1.00  --bmc1_ucm_init_mode                    2
% 1.41/1.00  --bmc1_ucm_cone_mode                    none
% 1.41/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.41/1.00  --bmc1_ucm_relax_model                  4
% 1.41/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.41/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.41/1.00  --bmc1_ucm_layered_model                none
% 1.41/1.00  --bmc1_ucm_max_lemma_size               10
% 1.41/1.00  
% 1.41/1.00  ------ AIG Options
% 1.41/1.00  
% 1.41/1.00  --aig_mode                              false
% 1.41/1.00  
% 1.41/1.00  ------ Instantiation Options
% 1.41/1.00  
% 1.41/1.00  --instantiation_flag                    true
% 1.41/1.00  --inst_sos_flag                         false
% 1.41/1.00  --inst_sos_phase                        true
% 1.41/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.41/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.41/1.00  --inst_lit_sel_side                     num_symb
% 1.41/1.00  --inst_solver_per_active                1400
% 1.41/1.00  --inst_solver_calls_frac                1.
% 1.41/1.00  --inst_passive_queue_type               priority_queues
% 1.41/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.41/1.00  --inst_passive_queues_freq              [25;2]
% 1.41/1.00  --inst_dismatching                      true
% 1.41/1.00  --inst_eager_unprocessed_to_passive     true
% 1.41/1.00  --inst_prop_sim_given                   true
% 1.41/1.00  --inst_prop_sim_new                     false
% 1.41/1.00  --inst_subs_new                         false
% 1.41/1.00  --inst_eq_res_simp                      false
% 1.41/1.00  --inst_subs_given                       false
% 1.41/1.00  --inst_orphan_elimination               true
% 1.41/1.00  --inst_learning_loop_flag               true
% 1.41/1.00  --inst_learning_start                   3000
% 1.41/1.00  --inst_learning_factor                  2
% 1.41/1.00  --inst_start_prop_sim_after_learn       3
% 1.41/1.00  --inst_sel_renew                        solver
% 1.41/1.00  --inst_lit_activity_flag                true
% 1.41/1.00  --inst_restr_to_given                   false
% 1.41/1.00  --inst_activity_threshold               500
% 1.41/1.00  --inst_out_proof                        true
% 1.41/1.00  
% 1.41/1.00  ------ Resolution Options
% 1.41/1.00  
% 1.41/1.00  --resolution_flag                       true
% 1.41/1.00  --res_lit_sel                           adaptive
% 1.41/1.00  --res_lit_sel_side                      none
% 1.41/1.00  --res_ordering                          kbo
% 1.41/1.00  --res_to_prop_solver                    active
% 1.41/1.00  --res_prop_simpl_new                    false
% 1.41/1.00  --res_prop_simpl_given                  true
% 1.41/1.00  --res_passive_queue_type                priority_queues
% 1.41/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.41/1.00  --res_passive_queues_freq               [15;5]
% 1.41/1.00  --res_forward_subs                      full
% 1.41/1.00  --res_backward_subs                     full
% 1.41/1.00  --res_forward_subs_resolution           true
% 1.41/1.00  --res_backward_subs_resolution          true
% 1.41/1.00  --res_orphan_elimination                true
% 1.41/1.00  --res_time_limit                        2.
% 1.41/1.00  --res_out_proof                         true
% 1.41/1.00  
% 1.41/1.00  ------ Superposition Options
% 1.41/1.00  
% 1.41/1.00  --superposition_flag                    true
% 1.41/1.00  --sup_passive_queue_type                priority_queues
% 1.41/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.41/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.41/1.00  --demod_completeness_check              fast
% 1.41/1.00  --demod_use_ground                      true
% 1.41/1.00  --sup_to_prop_solver                    passive
% 1.41/1.00  --sup_prop_simpl_new                    true
% 1.41/1.00  --sup_prop_simpl_given                  true
% 1.41/1.00  --sup_fun_splitting                     false
% 1.41/1.00  --sup_smt_interval                      50000
% 1.41/1.00  
% 1.41/1.00  ------ Superposition Simplification Setup
% 1.41/1.00  
% 1.41/1.00  --sup_indices_passive                   []
% 1.41/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.41/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.00  --sup_full_bw                           [BwDemod]
% 1.41/1.00  --sup_immed_triv                        [TrivRules]
% 1.41/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.41/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.00  --sup_immed_bw_main                     []
% 1.41/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.41/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.00  
% 1.41/1.00  ------ Combination Options
% 1.41/1.00  
% 1.41/1.00  --comb_res_mult                         3
% 1.41/1.00  --comb_sup_mult                         2
% 1.41/1.00  --comb_inst_mult                        10
% 1.41/1.00  
% 1.41/1.00  ------ Debug Options
% 1.41/1.00  
% 1.41/1.00  --dbg_backtrace                         false
% 1.41/1.00  --dbg_dump_prop_clauses                 false
% 1.41/1.00  --dbg_dump_prop_clauses_file            -
% 1.41/1.00  --dbg_out_stat                          false
% 1.41/1.00  ------ Parsing...
% 1.41/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.41/1.00  
% 1.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.41/1.00  
% 1.41/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.41/1.00  
% 1.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.41/1.00  ------ Proving...
% 1.41/1.00  ------ Problem Properties 
% 1.41/1.00  
% 1.41/1.00  
% 1.41/1.00  clauses                                 22
% 1.41/1.00  conjectures                             2
% 1.41/1.00  EPR                                     5
% 1.41/1.00  Horn                                    19
% 1.41/1.00  unary                                   2
% 1.41/1.00  binary                                  5
% 1.41/1.00  lits                                    74
% 1.41/1.00  lits eq                                 4
% 1.41/1.00  fd_pure                                 0
% 1.41/1.00  fd_pseudo                               0
% 1.41/1.00  fd_cond                                 0
% 1.41/1.00  fd_pseudo_cond                          1
% 1.41/1.00  AC symbols                              0
% 1.41/1.00  
% 1.41/1.00  ------ Schedule dynamic 5 is on 
% 1.41/1.00  
% 1.41/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.41/1.00  
% 1.41/1.00  
% 1.41/1.00  ------ 
% 1.41/1.00  Current options:
% 1.41/1.00  ------ 
% 1.41/1.00  
% 1.41/1.00  ------ Input Options
% 1.41/1.00  
% 1.41/1.00  --out_options                           all
% 1.41/1.00  --tptp_safe_out                         true
% 1.41/1.00  --problem_path                          ""
% 1.41/1.00  --include_path                          ""
% 1.41/1.00  --clausifier                            res/vclausify_rel
% 1.41/1.00  --clausifier_options                    --mode clausify
% 1.41/1.00  --stdin                                 false
% 1.41/1.00  --stats_out                             all
% 1.41/1.00  
% 1.41/1.00  ------ General Options
% 1.41/1.00  
% 1.41/1.00  --fof                                   false
% 1.41/1.00  --time_out_real                         305.
% 1.41/1.00  --time_out_virtual                      -1.
% 1.41/1.00  --symbol_type_check                     false
% 1.41/1.00  --clausify_out                          false
% 1.41/1.00  --sig_cnt_out                           false
% 1.41/1.00  --trig_cnt_out                          false
% 1.41/1.00  --trig_cnt_out_tolerance                1.
% 1.41/1.00  --trig_cnt_out_sk_spl                   false
% 1.41/1.00  --abstr_cl_out                          false
% 1.41/1.00  
% 1.41/1.00  ------ Global Options
% 1.41/1.00  
% 1.41/1.00  --schedule                              default
% 1.41/1.00  --add_important_lit                     false
% 1.41/1.00  --prop_solver_per_cl                    1000
% 1.41/1.00  --min_unsat_core                        false
% 1.41/1.00  --soft_assumptions                      false
% 1.41/1.00  --soft_lemma_size                       3
% 1.41/1.00  --prop_impl_unit_size                   0
% 1.41/1.00  --prop_impl_unit                        []
% 1.41/1.00  --share_sel_clauses                     true
% 1.41/1.00  --reset_solvers                         false
% 1.41/1.00  --bc_imp_inh                            [conj_cone]
% 1.41/1.00  --conj_cone_tolerance                   3.
% 1.41/1.00  --extra_neg_conj                        none
% 1.41/1.00  --large_theory_mode                     true
% 1.41/1.00  --prolific_symb_bound                   200
% 1.41/1.00  --lt_threshold                          2000
% 1.41/1.00  --clause_weak_htbl                      true
% 1.41/1.00  --gc_record_bc_elim                     false
% 1.41/1.00  
% 1.41/1.00  ------ Preprocessing Options
% 1.41/1.00  
% 1.41/1.00  --preprocessing_flag                    true
% 1.41/1.00  --time_out_prep_mult                    0.1
% 1.41/1.00  --splitting_mode                        input
% 1.41/1.00  --splitting_grd                         true
% 1.41/1.00  --splitting_cvd                         false
% 1.41/1.00  --splitting_cvd_svl                     false
% 1.41/1.00  --splitting_nvd                         32
% 1.41/1.00  --sub_typing                            true
% 1.41/1.00  --prep_gs_sim                           true
% 1.41/1.00  --prep_unflatten                        true
% 1.41/1.00  --prep_res_sim                          true
% 1.41/1.00  --prep_upred                            true
% 1.41/1.00  --prep_sem_filter                       exhaustive
% 1.41/1.00  --prep_sem_filter_out                   false
% 1.41/1.00  --pred_elim                             true
% 1.41/1.00  --res_sim_input                         true
% 1.41/1.00  --eq_ax_congr_red                       true
% 1.41/1.00  --pure_diseq_elim                       true
% 1.41/1.00  --brand_transform                       false
% 1.41/1.00  --non_eq_to_eq                          false
% 1.41/1.00  --prep_def_merge                        true
% 1.41/1.00  --prep_def_merge_prop_impl              false
% 1.41/1.00  --prep_def_merge_mbd                    true
% 1.41/1.00  --prep_def_merge_tr_red                 false
% 1.41/1.00  --prep_def_merge_tr_cl                  false
% 1.41/1.00  --smt_preprocessing                     true
% 1.41/1.00  --smt_ac_axioms                         fast
% 1.41/1.00  --preprocessed_out                      false
% 1.41/1.00  --preprocessed_stats                    false
% 1.41/1.00  
% 1.41/1.00  ------ Abstraction refinement Options
% 1.41/1.00  
% 1.41/1.00  --abstr_ref                             []
% 1.41/1.00  --abstr_ref_prep                        false
% 1.41/1.00  --abstr_ref_until_sat                   false
% 1.41/1.00  --abstr_ref_sig_restrict                funpre
% 1.41/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.41/1.00  --abstr_ref_under                       []
% 1.41/1.00  
% 1.41/1.00  ------ SAT Options
% 1.41/1.00  
% 1.41/1.00  --sat_mode                              false
% 1.41/1.00  --sat_fm_restart_options                ""
% 1.41/1.00  --sat_gr_def                            false
% 1.41/1.00  --sat_epr_types                         true
% 1.41/1.00  --sat_non_cyclic_types                  false
% 1.41/1.00  --sat_finite_models                     false
% 1.41/1.00  --sat_fm_lemmas                         false
% 1.41/1.00  --sat_fm_prep                           false
% 1.41/1.00  --sat_fm_uc_incr                        true
% 1.41/1.00  --sat_out_model                         small
% 1.41/1.00  --sat_out_clauses                       false
% 1.41/1.00  
% 1.41/1.00  ------ QBF Options
% 1.41/1.00  
% 1.41/1.00  --qbf_mode                              false
% 1.41/1.00  --qbf_elim_univ                         false
% 1.41/1.00  --qbf_dom_inst                          none
% 1.41/1.00  --qbf_dom_pre_inst                      false
% 1.41/1.00  --qbf_sk_in                             false
% 1.41/1.00  --qbf_pred_elim                         true
% 1.41/1.00  --qbf_split                             512
% 1.41/1.00  
% 1.41/1.00  ------ BMC1 Options
% 1.41/1.00  
% 1.41/1.00  --bmc1_incremental                      false
% 1.41/1.00  --bmc1_axioms                           reachable_all
% 1.41/1.00  --bmc1_min_bound                        0
% 1.41/1.00  --bmc1_max_bound                        -1
% 1.41/1.00  --bmc1_max_bound_default                -1
% 1.41/1.00  --bmc1_symbol_reachability              true
% 1.41/1.00  --bmc1_property_lemmas                  false
% 1.41/1.00  --bmc1_k_induction                      false
% 1.41/1.00  --bmc1_non_equiv_states                 false
% 1.41/1.00  --bmc1_deadlock                         false
% 1.41/1.00  --bmc1_ucm                              false
% 1.41/1.00  --bmc1_add_unsat_core                   none
% 1.41/1.00  --bmc1_unsat_core_children              false
% 1.41/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.41/1.00  --bmc1_out_stat                         full
% 1.41/1.00  --bmc1_ground_init                      false
% 1.41/1.00  --bmc1_pre_inst_next_state              false
% 1.41/1.00  --bmc1_pre_inst_state                   false
% 1.41/1.00  --bmc1_pre_inst_reach_state             false
% 1.41/1.00  --bmc1_out_unsat_core                   false
% 1.41/1.00  --bmc1_aig_witness_out                  false
% 1.41/1.00  --bmc1_verbose                          false
% 1.41/1.00  --bmc1_dump_clauses_tptp                false
% 1.41/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.41/1.00  --bmc1_dump_file                        -
% 1.41/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.41/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.41/1.00  --bmc1_ucm_extend_mode                  1
% 1.41/1.00  --bmc1_ucm_init_mode                    2
% 1.41/1.00  --bmc1_ucm_cone_mode                    none
% 1.41/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.41/1.00  --bmc1_ucm_relax_model                  4
% 1.41/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.41/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.41/1.00  --bmc1_ucm_layered_model                none
% 1.41/1.00  --bmc1_ucm_max_lemma_size               10
% 1.41/1.00  
% 1.41/1.00  ------ AIG Options
% 1.41/1.00  
% 1.41/1.00  --aig_mode                              false
% 1.41/1.00  
% 1.41/1.00  ------ Instantiation Options
% 1.41/1.00  
% 1.41/1.00  --instantiation_flag                    true
% 1.41/1.00  --inst_sos_flag                         false
% 1.41/1.00  --inst_sos_phase                        true
% 1.41/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.41/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.41/1.00  --inst_lit_sel_side                     none
% 1.41/1.00  --inst_solver_per_active                1400
% 1.41/1.00  --inst_solver_calls_frac                1.
% 1.41/1.00  --inst_passive_queue_type               priority_queues
% 1.41/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.41/1.00  --inst_passive_queues_freq              [25;2]
% 1.41/1.00  --inst_dismatching                      true
% 1.41/1.00  --inst_eager_unprocessed_to_passive     true
% 1.41/1.00  --inst_prop_sim_given                   true
% 1.41/1.00  --inst_prop_sim_new                     false
% 1.41/1.00  --inst_subs_new                         false
% 1.41/1.00  --inst_eq_res_simp                      false
% 1.41/1.00  --inst_subs_given                       false
% 1.41/1.00  --inst_orphan_elimination               true
% 1.41/1.00  --inst_learning_loop_flag               true
% 1.41/1.00  --inst_learning_start                   3000
% 1.41/1.00  --inst_learning_factor                  2
% 1.41/1.00  --inst_start_prop_sim_after_learn       3
% 1.41/1.00  --inst_sel_renew                        solver
% 1.41/1.00  --inst_lit_activity_flag                true
% 1.41/1.00  --inst_restr_to_given                   false
% 1.41/1.00  --inst_activity_threshold               500
% 1.41/1.00  --inst_out_proof                        true
% 1.41/1.00  
% 1.41/1.00  ------ Resolution Options
% 1.41/1.00  
% 1.41/1.00  --resolution_flag                       false
% 1.41/1.00  --res_lit_sel                           adaptive
% 1.41/1.00  --res_lit_sel_side                      none
% 1.41/1.00  --res_ordering                          kbo
% 1.41/1.00  --res_to_prop_solver                    active
% 1.41/1.00  --res_prop_simpl_new                    false
% 1.41/1.00  --res_prop_simpl_given                  true
% 1.41/1.00  --res_passive_queue_type                priority_queues
% 1.41/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.41/1.00  --res_passive_queues_freq               [15;5]
% 1.41/1.00  --res_forward_subs                      full
% 1.41/1.00  --res_backward_subs                     full
% 1.41/1.00  --res_forward_subs_resolution           true
% 1.41/1.00  --res_backward_subs_resolution          true
% 1.41/1.00  --res_orphan_elimination                true
% 1.41/1.00  --res_time_limit                        2.
% 1.41/1.00  --res_out_proof                         true
% 1.41/1.00  
% 1.41/1.00  ------ Superposition Options
% 1.41/1.00  
% 1.41/1.00  --superposition_flag                    true
% 1.41/1.00  --sup_passive_queue_type                priority_queues
% 1.41/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.41/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.41/1.00  --demod_completeness_check              fast
% 1.41/1.00  --demod_use_ground                      true
% 1.41/1.00  --sup_to_prop_solver                    passive
% 1.41/1.00  --sup_prop_simpl_new                    true
% 1.41/1.00  --sup_prop_simpl_given                  true
% 1.41/1.00  --sup_fun_splitting                     false
% 1.41/1.00  --sup_smt_interval                      50000
% 1.41/1.00  
% 1.41/1.00  ------ Superposition Simplification Setup
% 1.41/1.00  
% 1.41/1.00  --sup_indices_passive                   []
% 1.41/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.41/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.00  --sup_full_bw                           [BwDemod]
% 1.41/1.00  --sup_immed_triv                        [TrivRules]
% 1.41/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.41/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.00  --sup_immed_bw_main                     []
% 1.41/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.41/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.00  
% 1.41/1.00  ------ Combination Options
% 1.41/1.00  
% 1.41/1.00  --comb_res_mult                         3
% 1.41/1.00  --comb_sup_mult                         2
% 1.41/1.00  --comb_inst_mult                        10
% 1.41/1.00  
% 1.41/1.00  ------ Debug Options
% 1.41/1.00  
% 1.41/1.00  --dbg_backtrace                         false
% 1.41/1.00  --dbg_dump_prop_clauses                 false
% 1.41/1.00  --dbg_dump_prop_clauses_file            -
% 1.41/1.00  --dbg_out_stat                          false
% 1.41/1.00  
% 1.41/1.00  
% 1.41/1.00  
% 1.41/1.00  
% 1.41/1.00  ------ Proving...
% 1.41/1.00  
% 1.41/1.00  
% 1.41/1.00  % SZS status Theorem for theBenchmark.p
% 1.41/1.00  
% 1.41/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.41/1.00  
% 1.41/1.00  fof(f16,plain,(
% 1.41/1.00    ! [X2,X1,X0] : (sP1(X2,X1,X0) <=> ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))),
% 1.41/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.41/1.00  
% 1.41/1.00  fof(f25,plain,(
% 1.41/1.00    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0))) & (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | ~sP1(X2,X1,X0)))),
% 1.41/1.00    inference(nnf_transformation,[],[f16])).
% 1.41/1.00  
% 1.41/1.00  fof(f26,plain,(
% 1.41/1.00    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v6_orders_2(X3,X2))) & (? [X4] : (r2_hidden(X0,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X4,X2)) | ~sP1(X0,X1,X2)))),
% 1.41/1.00    inference(rectify,[],[f25])).
% 1.41/1.00  
% 1.41/1.00  fof(f27,plain,(
% 1.41/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X0,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X4,X2)) => (r2_hidden(X0,sK3(X0,X1,X2)) & r2_hidden(X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK3(X0,X1,X2),X2)))),
% 1.41/1.00    introduced(choice_axiom,[])).
% 1.41/1.00  
% 1.41/1.00  fof(f28,plain,(
% 1.41/1.00    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v6_orders_2(X3,X2))) & ((r2_hidden(X0,sK3(X0,X1,X2)) & r2_hidden(X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK3(X0,X1,X2),X2)) | ~sP1(X0,X1,X2)))),
% 1.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 1.41/1.00  
% 1.41/1.00  fof(f53,plain,(
% 1.41/1.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2) | ~r2_hidden(X0,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v6_orders_2(X3,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f28])).
% 1.41/1.00  
% 1.41/1.00  fof(f4,conjecture,(
% 1.41/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <=> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))))))),
% 1.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.41/1.00  
% 1.41/1.00  fof(f5,negated_conjecture,(
% 1.41/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <=> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))))))),
% 1.41/1.00    inference(negated_conjecture,[],[f4])).
% 1.41/1.00  
% 1.41/1.00  fof(f12,plain,(
% 1.41/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <~> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.41/1.00    inference(ennf_transformation,[],[f5])).
% 1.41/1.00  
% 1.41/1.00  fof(f13,plain,(
% 1.41/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <~> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.41/1.00    inference(flattening,[],[f12])).
% 1.41/1.00  
% 1.41/1.00  fof(f17,plain,(
% 1.41/1.00    ? [X0] : (? [X1] : (? [X2] : ((sP1(X2,X1,X0) <~> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.41/1.00    inference(definition_folding,[],[f13,f16])).
% 1.41/1.00  
% 1.41/1.00  fof(f29,plain,(
% 1.41/1.00    ? [X0] : (? [X1] : (? [X2] : (((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ~sP1(X2,X1,X0)) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | sP1(X2,X1,X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.41/1.00    inference(nnf_transformation,[],[f17])).
% 1.41/1.00  
% 1.41/1.00  fof(f30,plain,(
% 1.41/1.00    ? [X0] : (? [X1] : (? [X2] : ((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ~sP1(X2,X1,X0)) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | sP1(X2,X1,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.41/1.00    inference(flattening,[],[f29])).
% 1.41/1.00  
% 1.41/1.00  fof(f33,plain,(
% 1.41/1.00    ( ! [X0,X1] : (? [X2] : ((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ~sP1(X2,X1,X0)) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | sP1(X2,X1,X0)) & m1_subset_1(X2,u1_struct_0(X0))) => ((((r1_orders_2(X0,sK6,X1) | ~r2_orders_2(X0,X1,sK6)) & (~r1_orders_2(X0,sK6,X1) | r2_orders_2(X0,X1,sK6))) | ~sP1(sK6,X1,X0)) & (((r2_orders_2(X0,X1,sK6) | r1_orders_2(X0,sK6,X1)) & (~r1_orders_2(X0,sK6,X1) | ~r2_orders_2(X0,X1,sK6))) | sP1(sK6,X1,X0)) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 1.41/1.00    introduced(choice_axiom,[])).
% 1.41/1.00  
% 1.41/1.00  fof(f32,plain,(
% 1.41/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ~sP1(X2,X1,X0)) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | sP1(X2,X1,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((((r1_orders_2(X0,X2,sK5) | ~r2_orders_2(X0,sK5,X2)) & (~r1_orders_2(X0,X2,sK5) | r2_orders_2(X0,sK5,X2))) | ~sP1(X2,sK5,X0)) & (((r2_orders_2(X0,sK5,X2) | r1_orders_2(X0,X2,sK5)) & (~r1_orders_2(X0,X2,sK5) | ~r2_orders_2(X0,sK5,X2))) | sP1(X2,sK5,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.41/1.00    introduced(choice_axiom,[])).
% 1.41/1.00  
% 1.41/1.00  fof(f31,plain,(
% 1.41/1.00    ? [X0] : (? [X1] : (? [X2] : ((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ~sP1(X2,X1,X0)) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | sP1(X2,X1,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : ((((r1_orders_2(sK4,X2,X1) | ~r2_orders_2(sK4,X1,X2)) & (~r1_orders_2(sK4,X2,X1) | r2_orders_2(sK4,X1,X2))) | ~sP1(X2,X1,sK4)) & (((r2_orders_2(sK4,X1,X2) | r1_orders_2(sK4,X2,X1)) & (~r1_orders_2(sK4,X2,X1) | ~r2_orders_2(sK4,X1,X2))) | sP1(X2,X1,sK4)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v3_orders_2(sK4))),
% 1.41/1.00    introduced(choice_axiom,[])).
% 1.41/1.00  
% 1.41/1.00  fof(f34,plain,(
% 1.41/1.00    (((((r1_orders_2(sK4,sK6,sK5) | ~r2_orders_2(sK4,sK5,sK6)) & (~r1_orders_2(sK4,sK6,sK5) | r2_orders_2(sK4,sK5,sK6))) | ~sP1(sK6,sK5,sK4)) & (((r2_orders_2(sK4,sK5,sK6) | r1_orders_2(sK4,sK6,sK5)) & (~r1_orders_2(sK4,sK6,sK5) | ~r2_orders_2(sK4,sK5,sK6))) | sP1(sK6,sK5,sK4)) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v3_orders_2(sK4)),
% 1.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).
% 1.41/1.00  
% 1.41/1.00  fof(f60,plain,(
% 1.41/1.00    r2_orders_2(sK4,sK5,sK6) | r1_orders_2(sK4,sK6,sK5) | sP1(sK6,sK5,sK4)),
% 1.41/1.00    inference(cnf_transformation,[],[f34])).
% 1.41/1.00  
% 1.41/1.00  fof(f1,axiom,(
% 1.41/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.41/1.00  
% 1.41/1.00  fof(f7,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.41/1.00    inference(ennf_transformation,[],[f1])).
% 1.41/1.00  
% 1.41/1.00  fof(f18,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.41/1.00    inference(nnf_transformation,[],[f7])).
% 1.41/1.00  
% 1.41/1.00  fof(f19,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.41/1.00    inference(flattening,[],[f18])).
% 1.41/1.00  
% 1.41/1.00  fof(f35,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f19])).
% 1.41/1.00  
% 1.41/1.00  fof(f56,plain,(
% 1.41/1.00    l1_orders_2(sK4)),
% 1.41/1.00    inference(cnf_transformation,[],[f34])).
% 1.41/1.00  
% 1.41/1.00  fof(f57,plain,(
% 1.41/1.00    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.41/1.00    inference(cnf_transformation,[],[f34])).
% 1.41/1.00  
% 1.41/1.00  fof(f58,plain,(
% 1.41/1.00    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.41/1.00    inference(cnf_transformation,[],[f34])).
% 1.41/1.00  
% 1.41/1.00  fof(f51,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,sK3(X0,X1,X2)) | ~sP1(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f28])).
% 1.41/1.00  
% 1.41/1.00  fof(f50,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP1(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f28])).
% 1.41/1.00  
% 1.41/1.00  fof(f49,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (v6_orders_2(sK3(X0,X1,X2),X2) | ~sP1(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f28])).
% 1.41/1.00  
% 1.41/1.00  fof(f52,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,sK3(X0,X1,X2)) | ~sP1(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f28])).
% 1.41/1.00  
% 1.41/1.00  fof(f3,axiom,(
% 1.41/1.00    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 1.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.41/1.00  
% 1.41/1.00  fof(f6,plain,(
% 1.41/1.00    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 1.41/1.00    inference(rectify,[],[f3])).
% 1.41/1.00  
% 1.41/1.00  fof(f10,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.41/1.00    inference(ennf_transformation,[],[f6])).
% 1.41/1.00  
% 1.41/1.00  fof(f11,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.41/1.00    inference(flattening,[],[f10])).
% 1.41/1.00  
% 1.41/1.00  fof(f14,plain,(
% 1.41/1.00    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0))),
% 1.41/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.41/1.00  
% 1.41/1.00  fof(f15,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : ((sP0(X2,X1,X0) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.41/1.00    inference(definition_folding,[],[f11,f14])).
% 1.41/1.00  
% 1.41/1.00  fof(f24,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : ((sP0(X2,X1,X0) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.41/1.00    inference(rectify,[],[f15])).
% 1.41/1.00  
% 1.41/1.00  fof(f47,plain,(
% 1.41/1.00    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f24])).
% 1.41/1.00  
% 1.41/1.00  fof(f54,plain,(
% 1.41/1.00    v3_orders_2(sK4)),
% 1.41/1.00    inference(cnf_transformation,[],[f34])).
% 1.41/1.00  
% 1.41/1.00  fof(f20,plain,(
% 1.41/1.00    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0))),
% 1.41/1.00    inference(nnf_transformation,[],[f14])).
% 1.41/1.00  
% 1.41/1.00  fof(f21,plain,(
% 1.41/1.00    ! [X0,X1,X2] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) | (~r1_orders_2(X2,X0,X1) & ~r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2))),
% 1.41/1.00    inference(rectify,[],[f20])).
% 1.41/1.00  
% 1.41/1.00  fof(f22,plain,(
% 1.41/1.00    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) => (r2_hidden(X0,sK2(X0,X1,X2)) & r2_hidden(X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK2(X0,X1,X2),X2)))),
% 1.41/1.00    introduced(choice_axiom,[])).
% 1.41/1.00  
% 1.41/1.00  fof(f23,plain,(
% 1.41/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,sK2(X0,X1,X2)) & r2_hidden(X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK2(X0,X1,X2),X2)) | (~r1_orders_2(X2,X0,X1) & ~r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2))),
% 1.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 1.41/1.00  
% 1.41/1.00  fof(f43,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~r1_orders_2(X2,X1,X0) | ~sP0(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f23])).
% 1.41/1.00  
% 1.41/1.00  fof(f48,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f24])).
% 1.41/1.00  
% 1.41/1.00  fof(f45,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,sK2(X0,X1,X2)) | ~r1_orders_2(X2,X1,X0) | ~sP0(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f23])).
% 1.41/1.00  
% 1.41/1.00  fof(f46,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,sK2(X0,X1,X2)) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f23])).
% 1.41/1.00  
% 1.41/1.00  fof(f39,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (v6_orders_2(sK2(X0,X1,X2),X2) | ~r1_orders_2(X2,X1,X0) | ~sP0(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f23])).
% 1.41/1.00  
% 1.41/1.00  fof(f40,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (v6_orders_2(sK2(X0,X1,X2),X2) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f23])).
% 1.41/1.00  
% 1.41/1.00  fof(f41,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~r1_orders_2(X2,X1,X0) | ~sP0(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f23])).
% 1.41/1.00  
% 1.41/1.00  fof(f42,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f23])).
% 1.41/1.00  
% 1.41/1.00  fof(f44,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f23])).
% 1.41/1.00  
% 1.41/1.00  fof(f62,plain,(
% 1.41/1.00    r1_orders_2(sK4,sK6,sK5) | ~r2_orders_2(sK4,sK5,sK6) | ~sP1(sK6,sK5,sK4)),
% 1.41/1.00    inference(cnf_transformation,[],[f34])).
% 1.41/1.00  
% 1.41/1.00  fof(f37,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f19])).
% 1.41/1.00  
% 1.41/1.00  fof(f61,plain,(
% 1.41/1.00    ~r1_orders_2(sK4,sK6,sK5) | r2_orders_2(sK4,sK5,sK6) | ~sP1(sK6,sK5,sK4)),
% 1.41/1.00    inference(cnf_transformation,[],[f34])).
% 1.41/1.00  
% 1.41/1.00  fof(f2,axiom,(
% 1.41/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 1.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.41/1.00  
% 1.41/1.00  fof(f8,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.41/1.00    inference(ennf_transformation,[],[f2])).
% 1.41/1.00  
% 1.41/1.00  fof(f9,plain,(
% 1.41/1.00    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.41/1.00    inference(flattening,[],[f8])).
% 1.41/1.00  
% 1.41/1.00  fof(f38,plain,(
% 1.41/1.00    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.41/1.00    inference(cnf_transformation,[],[f9])).
% 1.41/1.00  
% 1.41/1.00  fof(f55,plain,(
% 1.41/1.00    v5_orders_2(sK4)),
% 1.41/1.00    inference(cnf_transformation,[],[f34])).
% 1.41/1.00  
% 1.41/1.00  cnf(c_14,plain,
% 1.41/1.00      ( sP1(X0,X1,X2)
% 1.41/1.00      | ~ v6_orders_2(X3,X2)
% 1.41/1.00      | ~ r2_hidden(X1,X3)
% 1.41/1.00      | ~ r2_hidden(X0,X3)
% 1.41/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
% 1.41/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2224,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45)
% 1.41/1.00      | ~ v6_orders_2(X2_46,X0_45)
% 1.41/1.00      | ~ r2_hidden(X0_46,X2_46)
% 1.41/1.00      | ~ r2_hidden(X1_46,X2_46)
% 1.41/1.00      | ~ m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(X0_45))) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2931,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,sK4)
% 1.41/1.00      | ~ v6_orders_2(sK2(sK6,sK5,sK4),sK4)
% 1.41/1.00      | ~ r2_hidden(X0_46,sK2(sK6,sK5,sK4))
% 1.41/1.00      | ~ r2_hidden(X1_46,sK2(sK6,sK5,sK4))
% 1.41/1.00      | ~ m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2224]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3981,plain,
% 1.41/1.00      ( sP1(sK6,sK5,sK4)
% 1.41/1.00      | ~ v6_orders_2(sK2(sK6,sK5,sK4),sK4)
% 1.41/1.00      | ~ r2_hidden(sK5,sK2(sK6,sK5,sK4))
% 1.41/1.00      | ~ r2_hidden(sK6,sK2(sK6,sK5,sK4))
% 1.41/1.00      | ~ m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2931]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3982,plain,
% 1.41/1.00      ( sP1(sK6,sK5,sK4) = iProver_top
% 1.41/1.00      | v6_orders_2(sK2(sK6,sK5,sK4),sK4) != iProver_top
% 1.41/1.00      | r2_hidden(sK5,sK2(sK6,sK5,sK4)) != iProver_top
% 1.41/1.00      | r2_hidden(sK6,sK2(sK6,sK5,sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3981]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_21,negated_conjecture,
% 1.41/1.00      ( sP1(sK6,sK5,sK4)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | r2_orders_2(sK4,sK5,sK6) ),
% 1.41/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2,plain,
% 1.41/1.00      ( r1_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ r2_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.41/1.00      | ~ l1_orders_2(X0) ),
% 1.41/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_25,negated_conjecture,
% 1.41/1.00      ( l1_orders_2(sK4) ),
% 1.41/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_395,plain,
% 1.41/1.00      ( r1_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ r2_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_25]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_396,plain,
% 1.41/1.00      ( r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | ~ r2_orders_2(sK4,X0,X1)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1162,plain,
% 1.41/1.00      ( sP1(sK6,sK5,sK4)
% 1.41/1.00      | r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | sK5 != X0
% 1.41/1.00      | sK6 != X1
% 1.41/1.00      | sK4 != sK4 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_396]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1163,plain,
% 1.41/1.00      ( sP1(sK6,sK5,sK4)
% 1.41/1.00      | r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_1162]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_24,negated_conjecture,
% 1.41/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_23,negated_conjecture,
% 1.41/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1165,plain,
% 1.41/1.00      ( sP1(sK6,sK5,sK4)
% 1.41/1.00      | r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) ),
% 1.41/1.00      inference(global_propositional_subsumption,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_1163,c_24,c_23]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2207,plain,
% 1.41/1.00      ( sP1(sK6,sK5,sK4)
% 1.41/1.00      | r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_1165]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2656,plain,
% 1.41/1.00      ( sP1(sK6,sK5,sK4) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2207]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_16,plain,
% 1.41/1.00      ( ~ sP1(X0,X1,X2) | r2_hidden(X1,sK3(X0,X1,X2)) ),
% 1.41/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2222,plain,
% 1.41/1.00      ( ~ sP1(X0_46,X1_46,X0_45)
% 1.41/1.00      | r2_hidden(X1_46,sK3(X0_46,X1_46,X0_45)) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2641,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45) != iProver_top
% 1.41/1.00      | r2_hidden(X1_46,sK3(X0_46,X1_46,X0_45)) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2222]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_17,plain,
% 1.41/1.00      ( ~ sP1(X0,X1,X2)
% 1.41/1.00      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
% 1.41/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2221,plain,
% 1.41/1.00      ( ~ sP1(X0_46,X1_46,X0_45)
% 1.41/1.00      | m1_subset_1(sK3(X0_46,X1_46,X0_45),k1_zfmisc_1(u1_struct_0(X0_45))) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2642,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45) != iProver_top
% 1.41/1.00      | m1_subset_1(sK3(X0_46,X1_46,X0_45),k1_zfmisc_1(u1_struct_0(X0_45))) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2221]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2639,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45) = iProver_top
% 1.41/1.00      | v6_orders_2(X2_46,X0_45) != iProver_top
% 1.41/1.00      | r2_hidden(X1_46,X2_46) != iProver_top
% 1.41/1.00      | r2_hidden(X0_46,X2_46) != iProver_top
% 1.41/1.00      | m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(X0_45))) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2224]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3076,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45) != iProver_top
% 1.41/1.00      | sP1(X2_46,X3_46,X0_45) = iProver_top
% 1.41/1.00      | v6_orders_2(sK3(X0_46,X1_46,X0_45),X0_45) != iProver_top
% 1.41/1.00      | r2_hidden(X3_46,sK3(X0_46,X1_46,X0_45)) != iProver_top
% 1.41/1.00      | r2_hidden(X2_46,sK3(X0_46,X1_46,X0_45)) != iProver_top ),
% 1.41/1.00      inference(superposition,[status(thm)],[c_2642,c_2639]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_18,plain,
% 1.41/1.00      ( ~ sP1(X0,X1,X2) | v6_orders_2(sK3(X0,X1,X2),X2) ),
% 1.41/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2220,plain,
% 1.41/1.00      ( ~ sP1(X0_46,X1_46,X0_45)
% 1.41/1.00      | v6_orders_2(sK3(X0_46,X1_46,X0_45),X0_45) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2250,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45) != iProver_top
% 1.41/1.00      | v6_orders_2(sK3(X0_46,X1_46,X0_45),X0_45) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2220]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3396,plain,
% 1.41/1.00      ( sP1(X2_46,X3_46,X0_45) = iProver_top
% 1.41/1.00      | sP1(X0_46,X1_46,X0_45) != iProver_top
% 1.41/1.00      | r2_hidden(X3_46,sK3(X0_46,X1_46,X0_45)) != iProver_top
% 1.41/1.00      | r2_hidden(X2_46,sK3(X0_46,X1_46,X0_45)) != iProver_top ),
% 1.41/1.00      inference(global_propositional_subsumption,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_3076,c_2250]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3397,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45) != iProver_top
% 1.41/1.00      | sP1(X2_46,X3_46,X0_45) = iProver_top
% 1.41/1.00      | r2_hidden(X3_46,sK3(X0_46,X1_46,X0_45)) != iProver_top
% 1.41/1.00      | r2_hidden(X2_46,sK3(X0_46,X1_46,X0_45)) != iProver_top ),
% 1.41/1.00      inference(renaming,[status(thm)],[c_3396]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3404,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45) != iProver_top
% 1.41/1.00      | sP1(X2_46,X1_46,X0_45) = iProver_top
% 1.41/1.00      | r2_hidden(X2_46,sK3(X0_46,X1_46,X0_45)) != iProver_top ),
% 1.41/1.00      inference(superposition,[status(thm)],[c_2641,c_3397]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3424,plain,
% 1.41/1.00      ( sP1(X0_46,X1_46,X0_45) != iProver_top
% 1.41/1.00      | sP1(X1_46,X1_46,X0_45) = iProver_top ),
% 1.41/1.00      inference(superposition,[status(thm)],[c_2641,c_3404]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3488,plain,
% 1.41/1.00      ( sP1(sK5,sK5,sK4) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 1.41/1.00      inference(superposition,[status(thm)],[c_2656,c_3424]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_31,plain,
% 1.41/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_32,plain,
% 1.41/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1421,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | v6_orders_2(sK3(X0,X1,X2),X2)
% 1.41/1.00      | sK5 != X1
% 1.41/1.00      | sK6 != X0
% 1.41/1.00      | sK4 != X2 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_1165]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1422,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | v6_orders_2(sK3(sK6,sK5,sK4),sK4) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_1421]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1423,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 1.41/1.00      | v6_orders_2(sK3(sK6,sK5,sK4),sK4) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1422]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1447,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
% 1.41/1.00      | sK5 != X1
% 1.41/1.00      | sK6 != X0
% 1.41/1.00      | sK4 != X2 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_1165]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1448,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_1447]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1449,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 1.41/1.00      | m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1448]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1473,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | r2_hidden(X0,sK3(X1,X0,X2))
% 1.41/1.00      | sK5 != X0
% 1.41/1.00      | sK6 != X1
% 1.41/1.00      | sK4 != X2 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_1165]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1474,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | r2_hidden(sK5,sK3(sK6,sK5,sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_1473]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1475,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 1.41/1.00      | r2_hidden(sK5,sK3(sK6,sK5,sK4)) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1474]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_15,plain,
% 1.41/1.00      ( ~ sP1(X0,X1,X2) | r2_hidden(X0,sK3(X0,X1,X2)) ),
% 1.41/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1499,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | r2_hidden(X0,sK3(X0,X1,X2))
% 1.41/1.00      | sK5 != X1
% 1.41/1.00      | sK6 != X0
% 1.41/1.00      | sK4 != X2 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_1165]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1500,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | r2_hidden(sK6,sK3(sK6,sK5,sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_1499]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1501,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 1.41/1.00      | r2_hidden(sK6,sK3(sK6,sK5,sK4)) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_13,plain,
% 1.41/1.00      ( r1_orders_2(X0,X1,X2)
% 1.41/1.00      | r1_orders_2(X0,X2,X1)
% 1.41/1.00      | ~ v6_orders_2(X3,X0)
% 1.41/1.00      | ~ r2_hidden(X2,X3)
% 1.41/1.00      | ~ r2_hidden(X1,X3)
% 1.41/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.41/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.41/1.00      | ~ v3_orders_2(X0)
% 1.41/1.00      | ~ l1_orders_2(X0) ),
% 1.41/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_27,negated_conjecture,
% 1.41/1.00      ( v3_orders_2(sK4) ),
% 1.41/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_325,plain,
% 1.41/1.00      ( r1_orders_2(X0,X1,X2)
% 1.41/1.00      | r1_orders_2(X0,X2,X1)
% 1.41/1.00      | ~ v6_orders_2(X3,X0)
% 1.41/1.00      | ~ r2_hidden(X2,X3)
% 1.41/1.00      | ~ r2_hidden(X1,X3)
% 1.41/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.41/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.41/1.00      | ~ l1_orders_2(X0)
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_326,plain,
% 1.41/1.00      ( r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r1_orders_2(sK4,X1,X0)
% 1.41/1.00      | ~ v6_orders_2(X2,sK4)
% 1.41/1.00      | ~ r2_hidden(X1,X2)
% 1.41/1.00      | ~ r2_hidden(X0,X2)
% 1.41/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ l1_orders_2(sK4) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_325]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_330,plain,
% 1.41/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.41/1.00      | ~ r2_hidden(X0,X2)
% 1.41/1.00      | ~ r2_hidden(X1,X2)
% 1.41/1.00      | ~ v6_orders_2(X2,sK4)
% 1.41/1.00      | r1_orders_2(sK4,X1,X0)
% 1.41/1.00      | r1_orders_2(sK4,X0,X1) ),
% 1.41/1.00      inference(global_propositional_subsumption,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_326,c_25]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_331,plain,
% 1.41/1.00      ( r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r1_orders_2(sK4,X1,X0)
% 1.41/1.00      | ~ v6_orders_2(X2,sK4)
% 1.41/1.00      | ~ r2_hidden(X0,X2)
% 1.41/1.00      | ~ r2_hidden(X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(renaming,[status(thm)],[c_330]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2217,plain,
% 1.41/1.00      ( r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | r1_orders_2(sK4,X1_46,X0_46)
% 1.41/1.00      | ~ v6_orders_2(X2_46,sK4)
% 1.41/1.00      | ~ r2_hidden(X0_46,X2_46)
% 1.41/1.00      | ~ r2_hidden(X1_46,X2_46)
% 1.41/1.00      | ~ m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_331]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3030,plain,
% 1.41/1.00      ( r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | r1_orders_2(sK4,X1_46,X0_46)
% 1.41/1.00      | ~ v6_orders_2(sK3(sK6,sK5,sK4),sK4)
% 1.41/1.00      | ~ r2_hidden(X0_46,sK3(sK6,sK5,sK4))
% 1.41/1.00      | ~ r2_hidden(X1_46,sK3(sK6,sK5,sK4))
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2217]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3385,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | ~ v6_orders_2(sK3(sK6,sK5,sK4),sK4)
% 1.41/1.00      | ~ r2_hidden(sK5,sK3(sK6,sK5,sK4))
% 1.41/1.00      | ~ r2_hidden(sK6,sK3(sK6,sK5,sK4))
% 1.41/1.00      | ~ m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_3030]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3386,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 1.41/1.00      | v6_orders_2(sK3(sK6,sK5,sK4),sK4) != iProver_top
% 1.41/1.00      | r2_hidden(sK5,sK3(sK6,sK5,sK4)) != iProver_top
% 1.41/1.00      | r2_hidden(sK6,sK3(sK6,sK5,sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK3(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3385]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3532,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 1.41/1.00      inference(global_propositional_subsumption,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_3488,c_31,c_32,c_1423,c_1449,c_1475,c_1501,c_3386]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2228,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0_45,X0_46,X1_46)
% 1.41/1.00      | r1_orders_2(X0_45,X2_46,X3_46)
% 1.41/1.00      | X2_46 != X0_46
% 1.41/1.00      | X3_46 != X1_46 ),
% 1.41/1.00      theory(equality) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3349,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | sK5 != X1_46
% 1.41/1.00      | sK6 != X0_46 ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2228]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3350,plain,
% 1.41/1.00      ( sK5 != X0_46
% 1.41/1.00      | sK6 != X1_46
% 1.41/1.00      | r1_orders_2(sK4,X1_46,X0_46) != iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3349]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3352,plain,
% 1.41/1.00      ( sK5 != sK5
% 1.41/1.00      | sK6 != sK5
% 1.41/1.00      | r1_orders_2(sK4,sK5,sK5) != iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_3350]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_7,plain,
% 1.41/1.00      ( ~ sP0(X0,X1,X2)
% 1.41/1.00      | ~ r1_orders_2(X2,X1,X0)
% 1.41/1.00      | r2_hidden(X1,sK2(X0,X1,X2)) ),
% 1.41/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_12,plain,
% 1.41/1.00      ( sP0(X0,X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 1.41/1.00      | ~ v3_orders_2(X2)
% 1.41/1.00      | ~ l1_orders_2(X2) ),
% 1.41/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_361,plain,
% 1.41/1.00      ( sP0(X0,X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 1.41/1.00      | ~ l1_orders_2(X2)
% 1.41/1.00      | sK4 != X2 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_362,plain,
% 1.41/1.00      ( sP0(X0,X1,sK4)
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ l1_orders_2(sK4) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_361]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_366,plain,
% 1.41/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | sP0(X0,X1,sK4) ),
% 1.41/1.00      inference(global_propositional_subsumption,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_362,c_25]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_367,plain,
% 1.41/1.00      ( sP0(X0,X1,sK4)
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(renaming,[status(thm)],[c_366]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_528,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | r2_hidden(X1,sK2(X2,X1,X0))
% 1.41/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.41/1.00      | X4 != X2
% 1.41/1.00      | X3 != X1
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_367]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_529,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r2_hidden(X0,sK2(X1,X0,sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_528]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2212,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | r2_hidden(X0_46,sK2(X1_46,X0_46,sK4))
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_529]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3127,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r2_hidden(sK5,sK2(sK6,sK5,sK4))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2212]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3149,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 1.41/1.00      | r2_hidden(sK5,sK2(sK6,sK5,sK4)) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3127]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_5,plain,
% 1.41/1.00      ( ~ sP0(X0,X1,X2)
% 1.41/1.00      | ~ r1_orders_2(X2,X1,X0)
% 1.41/1.00      | r2_hidden(X0,sK2(X0,X1,X2)) ),
% 1.41/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_562,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | r2_hidden(X2,sK2(X2,X1,X0))
% 1.41/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.41/1.00      | X4 != X2
% 1.41/1.00      | X3 != X1
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_367]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_563,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r2_hidden(X1,sK2(X1,X0,sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_562]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2210,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | r2_hidden(X1_46,sK2(X1_46,X0_46,sK4))
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_563]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3129,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r2_hidden(sK6,sK2(sK6,sK5,sK4))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2210]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3145,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 1.41/1.00      | r2_hidden(sK6,sK2(sK6,sK5,sK4)) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3129]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_4,plain,
% 1.41/1.00      ( ~ sP0(X0,X1,X2)
% 1.41/1.00      | ~ r1_orders_2(X2,X0,X1)
% 1.41/1.00      | r2_hidden(X0,sK2(X0,X1,X2)) ),
% 1.41/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_578,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | r2_hidden(X1,sK2(X1,X2,X0))
% 1.41/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.41/1.00      | X4 != X1
% 1.41/1.00      | X3 != X2
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_367]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_579,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r2_hidden(X0,sK2(X0,X1,sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_578]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2209,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | r2_hidden(X0_46,sK2(X0_46,X1_46,sK4))
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_579]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3130,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r2_hidden(sK5,sK2(sK5,sK6,sK4))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2209]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3143,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 1.41/1.00      | r2_hidden(sK5,sK2(sK5,sK6,sK4)) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3130]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_11,plain,
% 1.41/1.00      ( ~ sP0(X0,X1,X2)
% 1.41/1.00      | ~ r1_orders_2(X2,X1,X0)
% 1.41/1.00      | v6_orders_2(sK2(X0,X1,X2),X2) ),
% 1.41/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_460,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | v6_orders_2(sK2(X2,X1,X0),X0)
% 1.41/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.41/1.00      | X4 != X2
% 1.41/1.00      | X3 != X1
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_367]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_461,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | v6_orders_2(sK2(X1,X0,sK4),sK4)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_460]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2216,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | v6_orders_2(sK2(X1_46,X0_46,sK4),sK4)
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_461]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3131,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | v6_orders_2(sK2(sK6,sK5,sK4),sK4)
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2216]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3141,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 1.41/1.00      | v6_orders_2(sK2(sK6,sK5,sK4),sK4) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3131]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_10,plain,
% 1.41/1.00      ( ~ sP0(X0,X1,X2)
% 1.41/1.00      | ~ r1_orders_2(X2,X0,X1)
% 1.41/1.00      | v6_orders_2(sK2(X0,X1,X2),X2) ),
% 1.41/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_478,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | v6_orders_2(sK2(X1,X2,X0),X0)
% 1.41/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.41/1.00      | X4 != X1
% 1.41/1.00      | X3 != X2
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_367]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_479,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | v6_orders_2(sK2(X0,X1,sK4),sK4)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_478]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2215,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | v6_orders_2(sK2(X0_46,X1_46,sK4),sK4)
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_479]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3132,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | v6_orders_2(sK2(sK5,sK6,sK4),sK4)
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2215]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3139,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 1.41/1.00      | v6_orders_2(sK2(sK5,sK6,sK4),sK4) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3132]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_9,plain,
% 1.41/1.00      ( ~ sP0(X0,X1,X2)
% 1.41/1.00      | ~ r1_orders_2(X2,X1,X0)
% 1.41/1.00      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
% 1.41/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_494,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.41/1.00      | m1_subset_1(sK2(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.41/1.00      | X4 != X2
% 1.41/1.00      | X3 != X1
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_367]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_495,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | m1_subset_1(sK2(X1,X0,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_494]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2214,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 1.41/1.00      | m1_subset_1(sK2(X1_46,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_495]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3133,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2214]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3137,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 1.41/1.00      | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3133]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_8,plain,
% 1.41/1.00      ( ~ sP0(X0,X1,X2)
% 1.41/1.00      | ~ r1_orders_2(X2,X0,X1)
% 1.41/1.00      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ),
% 1.41/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_512,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.41/1.00      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.41/1.00      | X4 != X1
% 1.41/1.00      | X3 != X2
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_367]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_513,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | m1_subset_1(sK2(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2213,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 1.41/1.00      | m1_subset_1(sK2(X0_46,X1_46,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_513]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3134,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2213]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3135,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 1.41/1.00      | m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3134]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2941,plain,
% 1.41/1.00      ( r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | r1_orders_2(sK4,X1_46,X0_46)
% 1.41/1.00      | ~ v6_orders_2(sK2(sK5,sK6,sK4),sK4)
% 1.41/1.00      | ~ r2_hidden(X0_46,sK2(sK5,sK6,sK4))
% 1.41/1.00      | ~ r2_hidden(X1_46,sK2(sK5,sK6,sK4))
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2217]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2942,plain,
% 1.41/1.00      ( r1_orders_2(sK4,X0_46,X1_46) = iProver_top
% 1.41/1.00      | r1_orders_2(sK4,X1_46,X0_46) = iProver_top
% 1.41/1.00      | v6_orders_2(sK2(sK5,sK6,sK4),sK4) != iProver_top
% 1.41/1.00      | r2_hidden(X0_46,sK2(sK5,sK6,sK4)) != iProver_top
% 1.41/1.00      | r2_hidden(X1_46,sK2(sK5,sK6,sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2941]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2944,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK5,sK5) = iProver_top
% 1.41/1.00      | v6_orders_2(sK2(sK5,sK6,sK4),sK4) != iProver_top
% 1.41/1.00      | r2_hidden(sK5,sK2(sK5,sK6,sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK2(sK5,sK6,sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2942]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_6,plain,
% 1.41/1.00      ( ~ sP0(X0,X1,X2)
% 1.41/1.00      | ~ r1_orders_2(X2,X0,X1)
% 1.41/1.00      | r2_hidden(X1,sK2(X0,X1,X2)) ),
% 1.41/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_546,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | r2_hidden(X2,sK2(X1,X2,X0))
% 1.41/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.41/1.00      | X4 != X1
% 1.41/1.00      | X3 != X2
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_367]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_547,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r2_hidden(X1,sK2(X0,X1,sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_546]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2211,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0_46,X1_46)
% 1.41/1.00      | r2_hidden(X1_46,sK2(X0_46,X1_46,sK4))
% 1.41/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_547]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2880,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | r2_hidden(sK5,sK2(sK6,sK5,sK4))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2211]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2881,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK6,sK5) != iProver_top
% 1.41/1.00      | r2_hidden(sK5,sK2(sK6,sK5,sK4)) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2880]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2874,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | r2_hidden(sK6,sK2(sK6,sK5,sK4))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2209]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2875,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK6,sK5) != iProver_top
% 1.41/1.00      | r2_hidden(sK6,sK2(sK6,sK5,sK4)) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2874]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2868,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | v6_orders_2(sK2(sK6,sK5,sK4),sK4)
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2215]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2869,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK6,sK5) != iProver_top
% 1.41/1.00      | v6_orders_2(sK2(sK6,sK5,sK4),sK4) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2868]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2858,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2213]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2859,plain,
% 1.41/1.00      ( r1_orders_2(sK4,sK6,sK5) != iProver_top
% 1.41/1.00      | m1_subset_1(sK2(sK6,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 1.41/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 1.41/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2858]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_19,negated_conjecture,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | ~ r2_orders_2(sK4,sK5,sK6) ),
% 1.41/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_0,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | r2_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.41/1.00      | ~ l1_orders_2(X0)
% 1.41/1.00      | X2 = X1 ),
% 1.41/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_425,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | r2_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.41/1.00      | X2 = X1
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_25]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_426,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r2_orders_2(sK4,X0,X1)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | X1 = X0 ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_425]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1203,plain,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4)
% 1.41/1.00      | ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | X1 = X0
% 1.41/1.00      | sK5 != X0
% 1.41/1.00      | sK6 != X1
% 1.41/1.00      | sK4 != sK4 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_426]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1204,plain,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4)
% 1.41/1.00      | ~ r1_orders_2(sK4,sK5,sK6)
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.41/1.00      | sK6 = sK5 ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_1203]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_20,negated_conjecture,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4)
% 1.41/1.00      | ~ r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | r2_orders_2(sK4,sK5,sK6) ),
% 1.41/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_3,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ r2_orders_2(X0,X2,X1)
% 1.41/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.41/1.00      | ~ v5_orders_2(X0)
% 1.41/1.00      | ~ l1_orders_2(X0) ),
% 1.41/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_26,negated_conjecture,
% 1.41/1.00      ( v5_orders_2(sK4) ),
% 1.41/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_296,plain,
% 1.41/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.41/1.00      | ~ r2_orders_2(X0,X2,X1)
% 1.41/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.41/1.00      | ~ l1_orders_2(X0)
% 1.41/1.00      | sK4 != X0 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_297,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | ~ r2_orders_2(sK4,X1,X0)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ l1_orders_2(sK4) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_296]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_301,plain,
% 1.41/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ r2_orders_2(sK4,X1,X0)
% 1.41/1.00      | ~ r1_orders_2(sK4,X0,X1) ),
% 1.41/1.00      inference(global_propositional_subsumption,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_297,c_25]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_302,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | ~ r2_orders_2(sK4,X1,X0)
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(renaming,[status(thm)],[c_301]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1148,plain,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4)
% 1.41/1.00      | ~ r1_orders_2(sK4,X0,X1)
% 1.41/1.00      | ~ r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.41/1.00      | sK5 != X1
% 1.41/1.00      | sK6 != X0
% 1.41/1.00      | sK4 != sK4 ),
% 1.41/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_302]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1149,plain,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4)
% 1.41/1.00      | ~ r1_orders_2(sK4,sK6,sK5)
% 1.41/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.41/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.41/1.00      inference(unflattening,[status(thm)],[c_1148]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1151,plain,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4) | ~ r1_orders_2(sK4,sK6,sK5) ),
% 1.41/1.00      inference(global_propositional_subsumption,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_1149,c_24,c_23]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1206,plain,
% 1.41/1.00      ( ~ r1_orders_2(sK4,sK5,sK6) | ~ sP1(sK6,sK5,sK4) | sK6 = sK5 ),
% 1.41/1.00      inference(global_propositional_subsumption,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_1204,c_24,c_23,c_1149]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1207,plain,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4) | ~ r1_orders_2(sK4,sK5,sK6) | sK6 = sK5 ),
% 1.41/1.00      inference(renaming,[status(thm)],[c_1206]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2205,plain,
% 1.41/1.00      ( ~ sP1(sK6,sK5,sK4) | ~ r1_orders_2(sK4,sK5,sK6) | sK6 = sK5 ),
% 1.41/1.00      inference(subtyping,[status(esa)],[c_1207]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2275,plain,
% 1.41/1.00      ( sK6 = sK5
% 1.41/1.00      | sP1(sK6,sK5,sK4) != iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK5,sK6) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2205]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2226,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_2239,plain,
% 1.41/1.00      ( sK5 = sK5 ),
% 1.41/1.00      inference(instantiation,[status(thm)],[c_2226]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(c_1153,plain,
% 1.41/1.00      ( sP1(sK6,sK5,sK4) != iProver_top
% 1.41/1.00      | r1_orders_2(sK4,sK6,sK5) != iProver_top ),
% 1.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 1.41/1.00  
% 1.41/1.00  cnf(contradiction,plain,
% 1.41/1.00      ( $false ),
% 1.41/1.00      inference(minisat,
% 1.41/1.00                [status(thm)],
% 1.41/1.00                [c_3982,c_3532,c_3352,c_3149,c_3145,c_3143,c_3141,c_3139,
% 1.41/1.00                 c_3137,c_3135,c_2944,c_2881,c_2875,c_2869,c_2859,c_2275,
% 1.41/1.00                 c_2239,c_1153,c_32,c_31]) ).
% 1.41/1.00  
% 1.41/1.00  
% 1.41/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.41/1.00  
% 1.41/1.00  ------                               Statistics
% 1.41/1.00  
% 1.41/1.00  ------ General
% 1.41/1.00  
% 1.41/1.00  abstr_ref_over_cycles:                  0
% 1.41/1.00  abstr_ref_under_cycles:                 0
% 1.41/1.00  gc_basic_clause_elim:                   0
% 1.41/1.00  forced_gc_time:                         0
% 1.41/1.00  parsing_time:                           0.016
% 1.41/1.00  unif_index_cands_time:                  0.
% 1.41/1.00  unif_index_add_time:                    0.
% 1.41/1.00  orderings_time:                         0.
% 1.41/1.00  out_proof_time:                         0.011
% 1.41/1.00  total_time:                             0.157
% 1.41/1.00  num_of_symbols:                         48
% 1.41/1.00  num_of_terms:                           1855
% 1.41/1.00  
% 1.41/1.00  ------ Preprocessing
% 1.41/1.00  
% 1.41/1.00  num_of_splits:                          0
% 1.41/1.00  num_of_split_atoms:                     0
% 1.41/1.00  num_of_reused_defs:                     0
% 1.41/1.00  num_eq_ax_congr_red:                    30
% 1.41/1.00  num_of_sem_filtered_clauses:            1
% 1.41/1.00  num_of_subtypes:                        3
% 1.41/1.00  monotx_restored_types:                  0
% 1.41/1.00  sat_num_of_epr_types:                   0
% 1.41/1.00  sat_num_of_non_cyclic_types:            0
% 1.41/1.00  sat_guarded_non_collapsed_types:        1
% 1.41/1.00  num_pure_diseq_elim:                    0
% 1.41/1.00  simp_replaced_by:                       0
% 1.41/1.00  res_preprocessed:                       109
% 1.41/1.00  prep_upred:                             0
% 1.41/1.00  prep_unflattend:                        158
% 1.41/1.00  smt_new_axioms:                         0
% 1.41/1.00  pred_elim_cands:                        5
% 1.41/1.00  pred_elim:                              5
% 1.41/1.00  pred_elim_cl:                           6
% 1.41/1.00  pred_elim_cycles:                       10
% 1.41/1.00  merged_defs:                            0
% 1.41/1.00  merged_defs_ncl:                        0
% 1.41/1.00  bin_hyper_res:                          0
% 1.41/1.00  prep_cycles:                            4
% 1.41/1.00  pred_elim_time:                         0.044
% 1.41/1.00  splitting_time:                         0.
% 1.41/1.00  sem_filter_time:                        0.
% 1.41/1.00  monotx_time:                            0.
% 1.41/1.00  subtype_inf_time:                       0.
% 1.41/1.00  
% 1.41/1.00  ------ Problem properties
% 1.41/1.00  
% 1.41/1.00  clauses:                                22
% 1.41/1.00  conjectures:                            2
% 1.41/1.00  epr:                                    5
% 1.41/1.00  horn:                                   19
% 1.41/1.00  ground:                                 7
% 1.41/1.00  unary:                                  2
% 1.41/1.00  binary:                                 5
% 1.41/1.00  lits:                                   74
% 1.41/1.00  lits_eq:                                4
% 1.41/1.00  fd_pure:                                0
% 1.41/1.00  fd_pseudo:                              0
% 1.41/1.00  fd_cond:                                0
% 1.41/1.00  fd_pseudo_cond:                         1
% 1.41/1.00  ac_symbols:                             0
% 1.41/1.00  
% 1.41/1.00  ------ Propositional Solver
% 1.41/1.00  
% 1.41/1.00  prop_solver_calls:                      29
% 1.41/1.00  prop_fast_solver_calls:                 1353
% 1.41/1.00  smt_solver_calls:                       0
% 1.41/1.00  smt_fast_solver_calls:                  0
% 1.41/1.00  prop_num_of_clauses:                    728
% 1.41/1.00  prop_preprocess_simplified:             3842
% 1.41/1.00  prop_fo_subsumed:                       33
% 1.41/1.00  prop_solver_time:                       0.
% 1.41/1.00  smt_solver_time:                        0.
% 1.41/1.00  smt_fast_solver_time:                   0.
% 1.41/1.00  prop_fast_solver_time:                  0.
% 1.41/1.00  prop_unsat_core_time:                   0.
% 1.41/1.00  
% 1.41/1.00  ------ QBF
% 1.41/1.00  
% 1.41/1.00  qbf_q_res:                              0
% 1.41/1.00  qbf_num_tautologies:                    0
% 1.41/1.00  qbf_prep_cycles:                        0
% 1.41/1.00  
% 1.41/1.00  ------ BMC1
% 1.41/1.00  
% 1.41/1.00  bmc1_current_bound:                     -1
% 1.41/1.00  bmc1_last_solved_bound:                 -1
% 1.41/1.00  bmc1_unsat_core_size:                   -1
% 1.41/1.00  bmc1_unsat_core_parents_size:           -1
% 1.41/1.00  bmc1_merge_next_fun:                    0
% 1.41/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.41/1.00  
% 1.41/1.00  ------ Instantiation
% 1.41/1.00  
% 1.41/1.00  inst_num_of_clauses:                    148
% 1.41/1.00  inst_num_in_passive:                    21
% 1.41/1.00  inst_num_in_active:                     124
% 1.41/1.00  inst_num_in_unprocessed:                2
% 1.41/1.00  inst_num_of_loops:                      195
% 1.41/1.00  inst_num_of_learning_restarts:          0
% 1.41/1.00  inst_num_moves_active_passive:          64
% 1.41/1.00  inst_lit_activity:                      0
% 1.41/1.00  inst_lit_activity_moves:                0
% 1.41/1.00  inst_num_tautologies:                   0
% 1.41/1.00  inst_num_prop_implied:                  0
% 1.41/1.00  inst_num_existing_simplified:           0
% 1.41/1.00  inst_num_eq_res_simplified:             0
% 1.41/1.00  inst_num_child_elim:                    0
% 1.41/1.00  inst_num_of_dismatching_blockings:      10
% 1.41/1.00  inst_num_of_non_proper_insts:           203
% 1.41/1.00  inst_num_of_duplicates:                 0
% 1.41/1.00  inst_inst_num_from_inst_to_res:         0
% 1.41/1.00  inst_dismatching_checking_time:         0.
% 1.41/1.00  
% 1.41/1.00  ------ Resolution
% 1.41/1.00  
% 1.41/1.00  res_num_of_clauses:                     0
% 1.41/1.00  res_num_in_passive:                     0
% 1.41/1.00  res_num_in_active:                      0
% 1.41/1.00  res_num_of_loops:                       113
% 1.41/1.00  res_forward_subset_subsumed:            15
% 1.41/1.00  res_backward_subset_subsumed:           0
% 1.41/1.00  res_forward_subsumed:                   1
% 1.41/1.00  res_backward_subsumed:                  0
% 1.41/1.00  res_forward_subsumption_resolution:     3
% 1.41/1.00  res_backward_subsumption_resolution:    0
% 1.41/1.00  res_clause_to_clause_subsumption:       342
% 1.41/1.00  res_orphan_elimination:                 0
% 1.41/1.00  res_tautology_del:                      57
% 1.41/1.00  res_num_eq_res_simplified:              0
% 1.41/1.00  res_num_sel_changes:                    0
% 1.41/1.00  res_moves_from_active_to_pass:          0
% 1.41/1.00  
% 1.41/1.00  ------ Superposition
% 1.41/1.00  
% 1.41/1.00  sup_time_total:                         0.
% 1.41/1.00  sup_time_generating:                    0.
% 1.41/1.00  sup_time_sim_full:                      0.
% 1.41/1.00  sup_time_sim_immed:                     0.
% 1.41/1.00  
% 1.41/1.00  sup_num_of_clauses:                     52
% 1.41/1.00  sup_num_in_active:                      38
% 1.41/1.00  sup_num_in_passive:                     14
% 1.41/1.00  sup_num_of_loops:                       38
% 1.41/1.00  sup_fw_superposition:                   35
% 1.41/1.00  sup_bw_superposition:                   11
% 1.41/1.00  sup_immediate_simplified:               12
% 1.41/1.00  sup_given_eliminated:                   0
% 1.41/1.00  comparisons_done:                       0
% 1.41/1.00  comparisons_avoided:                    0
% 1.41/1.00  
% 1.41/1.00  ------ Simplifications
% 1.41/1.00  
% 1.41/1.00  
% 1.41/1.00  sim_fw_subset_subsumed:                 2
% 1.41/1.00  sim_bw_subset_subsumed:                 0
% 1.41/1.00  sim_fw_subsumed:                        7
% 1.41/1.00  sim_bw_subsumed:                        3
% 1.41/1.00  sim_fw_subsumption_res:                 2
% 1.41/1.00  sim_bw_subsumption_res:                 0
% 1.41/1.00  sim_tautology_del:                      2
% 1.41/1.00  sim_eq_tautology_del:                   0
% 1.41/1.00  sim_eq_res_simp:                        0
% 1.41/1.01  sim_fw_demodulated:                     0
% 1.41/1.01  sim_bw_demodulated:                     0
% 1.41/1.01  sim_light_normalised:                   0
% 1.41/1.01  sim_joinable_taut:                      0
% 1.41/1.01  sim_joinable_simp:                      0
% 1.41/1.01  sim_ac_normalised:                      0
% 1.41/1.01  sim_smt_subsumption:                    0
% 1.41/1.01  
%------------------------------------------------------------------------------

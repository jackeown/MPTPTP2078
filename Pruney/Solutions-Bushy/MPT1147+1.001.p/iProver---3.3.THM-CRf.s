%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1147+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:01 EST 2020

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

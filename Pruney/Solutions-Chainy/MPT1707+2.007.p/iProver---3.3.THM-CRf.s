%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:48 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 560 expanded)
%              Number of clauses        :   61 ( 124 expanded)
%              Number of leaves         :   12 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          :  577 (5261 expanded)
%              Number of equality atoms :  118 ( 985 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,conjecture,(
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
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) )
          & ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
     => ( ! [X4] :
            ( sK4 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        & ! [X5] :
            ( sK4 != X5
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            & ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3))) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2))) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2))) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ! [X4] :
        ( sK4 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
    & ! [X5] :
        ( sK4 != X5
        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
    & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f30,f29,f28,f27])).

fof(f55,plain,(
    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X4] :
      ( sK4 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f57])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X5] :
      ( sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f56])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_388,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_389,plain,
    ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_1114,plain,
    ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1124,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1122,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(k1_tsep_1(X1,X2,X0))
    | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_143,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_16,c_15,c_14])).

cnf(c_144,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_143])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_446,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_144,c_24])).

cnf(c_447,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X1,sK1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(sK1,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_451,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK1)
    | ~ m1_pre_topc(X0,sK1)
    | u1_struct_0(k1_tsep_1(sK1,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_25])).

cnf(c_452,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X1,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(k1_tsep_1(sK1,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_1112,plain,
    ( u1_struct_0(k1_tsep_1(sK1,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_2293,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1112])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3958,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2293,c_28])).

cnf(c_3959,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3958])).

cnf(c_3967,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_3959])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1362,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_1564,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_4294,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3967,c_23,c_22,c_21,c_20,c_1564])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1126,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4297,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4294,c_1126])).

cnf(c_9331,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_4297])).

cnf(c_6,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1125,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4300,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4294,c_1125])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_361,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | u1_struct_0(sK3) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_362,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_363,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_398,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_399,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_400,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_5738,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4300,c_363,c_400])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_153,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_11])).

cnf(c_154,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_371,plain,
    ( ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_154,c_18])).

cnf(c_372,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_373,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,X1)
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_154,c_17])).

cnf(c_355,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_356,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9331,c_5738,c_373,c_356])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.73/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/1.00  
% 2.73/1.00  ------  iProver source info
% 2.73/1.00  
% 2.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/1.00  git: non_committed_changes: false
% 2.73/1.00  git: last_make_outside_of_git: false
% 2.73/1.00  
% 2.73/1.00  ------ 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options
% 2.73/1.00  
% 2.73/1.00  --out_options                           all
% 2.73/1.00  --tptp_safe_out                         true
% 2.73/1.00  --problem_path                          ""
% 2.73/1.00  --include_path                          ""
% 2.73/1.00  --clausifier                            res/vclausify_rel
% 2.73/1.00  --clausifier_options                    --mode clausify
% 2.73/1.00  --stdin                                 false
% 2.73/1.00  --stats_out                             all
% 2.73/1.00  
% 2.73/1.00  ------ General Options
% 2.73/1.00  
% 2.73/1.00  --fof                                   false
% 2.73/1.00  --time_out_real                         305.
% 2.73/1.00  --time_out_virtual                      -1.
% 2.73/1.00  --symbol_type_check                     false
% 2.73/1.00  --clausify_out                          false
% 2.73/1.00  --sig_cnt_out                           false
% 2.73/1.00  --trig_cnt_out                          false
% 2.73/1.00  --trig_cnt_out_tolerance                1.
% 2.73/1.00  --trig_cnt_out_sk_spl                   false
% 2.73/1.00  --abstr_cl_out                          false
% 2.73/1.00  
% 2.73/1.00  ------ Global Options
% 2.73/1.00  
% 2.73/1.00  --schedule                              default
% 2.73/1.00  --add_important_lit                     false
% 2.73/1.00  --prop_solver_per_cl                    1000
% 2.73/1.00  --min_unsat_core                        false
% 2.73/1.00  --soft_assumptions                      false
% 2.73/1.00  --soft_lemma_size                       3
% 2.73/1.00  --prop_impl_unit_size                   0
% 2.73/1.00  --prop_impl_unit                        []
% 2.73/1.00  --share_sel_clauses                     true
% 2.73/1.00  --reset_solvers                         false
% 2.73/1.00  --bc_imp_inh                            [conj_cone]
% 2.73/1.00  --conj_cone_tolerance                   3.
% 2.73/1.00  --extra_neg_conj                        none
% 2.73/1.00  --large_theory_mode                     true
% 2.73/1.00  --prolific_symb_bound                   200
% 2.73/1.00  --lt_threshold                          2000
% 2.73/1.00  --clause_weak_htbl                      true
% 2.73/1.00  --gc_record_bc_elim                     false
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing Options
% 2.73/1.00  
% 2.73/1.00  --preprocessing_flag                    true
% 2.73/1.00  --time_out_prep_mult                    0.1
% 2.73/1.00  --splitting_mode                        input
% 2.73/1.00  --splitting_grd                         true
% 2.73/1.00  --splitting_cvd                         false
% 2.73/1.00  --splitting_cvd_svl                     false
% 2.73/1.00  --splitting_nvd                         32
% 2.73/1.00  --sub_typing                            true
% 2.73/1.00  --prep_gs_sim                           true
% 2.73/1.00  --prep_unflatten                        true
% 2.73/1.00  --prep_res_sim                          true
% 2.73/1.00  --prep_upred                            true
% 2.73/1.00  --prep_sem_filter                       exhaustive
% 2.73/1.00  --prep_sem_filter_out                   false
% 2.73/1.00  --pred_elim                             true
% 2.73/1.00  --res_sim_input                         true
% 2.73/1.00  --eq_ax_congr_red                       true
% 2.73/1.00  --pure_diseq_elim                       true
% 2.73/1.00  --brand_transform                       false
% 2.73/1.00  --non_eq_to_eq                          false
% 2.73/1.00  --prep_def_merge                        true
% 2.73/1.00  --prep_def_merge_prop_impl              false
% 2.73/1.00  --prep_def_merge_mbd                    true
% 2.73/1.00  --prep_def_merge_tr_red                 false
% 2.73/1.00  --prep_def_merge_tr_cl                  false
% 2.73/1.00  --smt_preprocessing                     true
% 2.73/1.00  --smt_ac_axioms                         fast
% 2.73/1.00  --preprocessed_out                      false
% 2.73/1.00  --preprocessed_stats                    false
% 2.73/1.00  
% 2.73/1.00  ------ Abstraction refinement Options
% 2.73/1.00  
% 2.73/1.00  --abstr_ref                             []
% 2.73/1.00  --abstr_ref_prep                        false
% 2.73/1.00  --abstr_ref_until_sat                   false
% 2.73/1.00  --abstr_ref_sig_restrict                funpre
% 2.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.00  --abstr_ref_under                       []
% 2.73/1.00  
% 2.73/1.00  ------ SAT Options
% 2.73/1.00  
% 2.73/1.00  --sat_mode                              false
% 2.73/1.00  --sat_fm_restart_options                ""
% 2.73/1.00  --sat_gr_def                            false
% 2.73/1.00  --sat_epr_types                         true
% 2.73/1.00  --sat_non_cyclic_types                  false
% 2.73/1.00  --sat_finite_models                     false
% 2.73/1.00  --sat_fm_lemmas                         false
% 2.73/1.00  --sat_fm_prep                           false
% 2.73/1.00  --sat_fm_uc_incr                        true
% 2.73/1.00  --sat_out_model                         small
% 2.73/1.00  --sat_out_clauses                       false
% 2.73/1.00  
% 2.73/1.00  ------ QBF Options
% 2.73/1.00  
% 2.73/1.00  --qbf_mode                              false
% 2.73/1.00  --qbf_elim_univ                         false
% 2.73/1.00  --qbf_dom_inst                          none
% 2.73/1.00  --qbf_dom_pre_inst                      false
% 2.73/1.00  --qbf_sk_in                             false
% 2.73/1.00  --qbf_pred_elim                         true
% 2.73/1.00  --qbf_split                             512
% 2.73/1.00  
% 2.73/1.00  ------ BMC1 Options
% 2.73/1.00  
% 2.73/1.00  --bmc1_incremental                      false
% 2.73/1.00  --bmc1_axioms                           reachable_all
% 2.73/1.00  --bmc1_min_bound                        0
% 2.73/1.00  --bmc1_max_bound                        -1
% 2.73/1.00  --bmc1_max_bound_default                -1
% 2.73/1.00  --bmc1_symbol_reachability              true
% 2.73/1.00  --bmc1_property_lemmas                  false
% 2.73/1.00  --bmc1_k_induction                      false
% 2.73/1.00  --bmc1_non_equiv_states                 false
% 2.73/1.00  --bmc1_deadlock                         false
% 2.73/1.00  --bmc1_ucm                              false
% 2.73/1.00  --bmc1_add_unsat_core                   none
% 2.73/1.00  --bmc1_unsat_core_children              false
% 2.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.00  --bmc1_out_stat                         full
% 2.73/1.00  --bmc1_ground_init                      false
% 2.73/1.00  --bmc1_pre_inst_next_state              false
% 2.73/1.00  --bmc1_pre_inst_state                   false
% 2.73/1.00  --bmc1_pre_inst_reach_state             false
% 2.73/1.00  --bmc1_out_unsat_core                   false
% 2.73/1.00  --bmc1_aig_witness_out                  false
% 2.73/1.00  --bmc1_verbose                          false
% 2.73/1.00  --bmc1_dump_clauses_tptp                false
% 2.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.00  --bmc1_dump_file                        -
% 2.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.00  --bmc1_ucm_extend_mode                  1
% 2.73/1.00  --bmc1_ucm_init_mode                    2
% 2.73/1.00  --bmc1_ucm_cone_mode                    none
% 2.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.00  --bmc1_ucm_relax_model                  4
% 2.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.00  --bmc1_ucm_layered_model                none
% 2.73/1.00  --bmc1_ucm_max_lemma_size               10
% 2.73/1.00  
% 2.73/1.00  ------ AIG Options
% 2.73/1.00  
% 2.73/1.00  --aig_mode                              false
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation Options
% 2.73/1.00  
% 2.73/1.00  --instantiation_flag                    true
% 2.73/1.00  --inst_sos_flag                         false
% 2.73/1.00  --inst_sos_phase                        true
% 2.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel_side                     num_symb
% 2.73/1.00  --inst_solver_per_active                1400
% 2.73/1.00  --inst_solver_calls_frac                1.
% 2.73/1.00  --inst_passive_queue_type               priority_queues
% 2.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.00  --inst_passive_queues_freq              [25;2]
% 2.73/1.00  --inst_dismatching                      true
% 2.73/1.00  --inst_eager_unprocessed_to_passive     true
% 2.73/1.00  --inst_prop_sim_given                   true
% 2.73/1.00  --inst_prop_sim_new                     false
% 2.73/1.00  --inst_subs_new                         false
% 2.73/1.00  --inst_eq_res_simp                      false
% 2.73/1.00  --inst_subs_given                       false
% 2.73/1.00  --inst_orphan_elimination               true
% 2.73/1.00  --inst_learning_loop_flag               true
% 2.73/1.00  --inst_learning_start                   3000
% 2.73/1.00  --inst_learning_factor                  2
% 2.73/1.00  --inst_start_prop_sim_after_learn       3
% 2.73/1.00  --inst_sel_renew                        solver
% 2.73/1.00  --inst_lit_activity_flag                true
% 2.73/1.00  --inst_restr_to_given                   false
% 2.73/1.00  --inst_activity_threshold               500
% 2.73/1.00  --inst_out_proof                        true
% 2.73/1.00  
% 2.73/1.00  ------ Resolution Options
% 2.73/1.00  
% 2.73/1.00  --resolution_flag                       true
% 2.73/1.00  --res_lit_sel                           adaptive
% 2.73/1.00  --res_lit_sel_side                      none
% 2.73/1.00  --res_ordering                          kbo
% 2.73/1.00  --res_to_prop_solver                    active
% 2.73/1.00  --res_prop_simpl_new                    false
% 2.73/1.00  --res_prop_simpl_given                  true
% 2.73/1.00  --res_passive_queue_type                priority_queues
% 2.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.00  --res_passive_queues_freq               [15;5]
% 2.73/1.00  --res_forward_subs                      full
% 2.73/1.00  --res_backward_subs                     full
% 2.73/1.00  --res_forward_subs_resolution           true
% 2.73/1.00  --res_backward_subs_resolution          true
% 2.73/1.00  --res_orphan_elimination                true
% 2.73/1.00  --res_time_limit                        2.
% 2.73/1.00  --res_out_proof                         true
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Options
% 2.73/1.00  
% 2.73/1.00  --superposition_flag                    true
% 2.73/1.00  --sup_passive_queue_type                priority_queues
% 2.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.00  --demod_completeness_check              fast
% 2.73/1.00  --demod_use_ground                      true
% 2.73/1.00  --sup_to_prop_solver                    passive
% 2.73/1.00  --sup_prop_simpl_new                    true
% 2.73/1.00  --sup_prop_simpl_given                  true
% 2.73/1.00  --sup_fun_splitting                     false
% 2.73/1.00  --sup_smt_interval                      50000
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Simplification Setup
% 2.73/1.00  
% 2.73/1.00  --sup_indices_passive                   []
% 2.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_full_bw                           [BwDemod]
% 2.73/1.00  --sup_immed_triv                        [TrivRules]
% 2.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_immed_bw_main                     []
% 2.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  
% 2.73/1.00  ------ Combination Options
% 2.73/1.00  
% 2.73/1.00  --comb_res_mult                         3
% 2.73/1.00  --comb_sup_mult                         2
% 2.73/1.00  --comb_inst_mult                        10
% 2.73/1.00  
% 2.73/1.00  ------ Debug Options
% 2.73/1.00  
% 2.73/1.00  --dbg_backtrace                         false
% 2.73/1.00  --dbg_dump_prop_clauses                 false
% 2.73/1.00  --dbg_dump_prop_clauses_file            -
% 2.73/1.00  --dbg_out_stat                          false
% 2.73/1.00  ------ Parsing...
% 2.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/1.00  ------ Proving...
% 2.73/1.00  ------ Problem Properties 
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  clauses                                 26
% 2.73/1.00  conjectures                             5
% 2.73/1.00  EPR                                     6
% 2.73/1.00  Horn                                    18
% 2.73/1.00  unary                                   7
% 2.73/1.00  binary                                  9
% 2.73/1.00  lits                                    70
% 2.73/1.00  lits eq                                 10
% 2.73/1.00  fd_pure                                 0
% 2.73/1.00  fd_pseudo                               0
% 2.73/1.00  fd_cond                                 0
% 2.73/1.00  fd_pseudo_cond                          4
% 2.73/1.00  AC symbols                              0
% 2.73/1.00  
% 2.73/1.00  ------ Schedule dynamic 5 is on 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  ------ 
% 2.73/1.00  Current options:
% 2.73/1.00  ------ 
% 2.73/1.00  
% 2.73/1.00  ------ Input Options
% 2.73/1.00  
% 2.73/1.00  --out_options                           all
% 2.73/1.00  --tptp_safe_out                         true
% 2.73/1.00  --problem_path                          ""
% 2.73/1.00  --include_path                          ""
% 2.73/1.00  --clausifier                            res/vclausify_rel
% 2.73/1.00  --clausifier_options                    --mode clausify
% 2.73/1.00  --stdin                                 false
% 2.73/1.00  --stats_out                             all
% 2.73/1.00  
% 2.73/1.00  ------ General Options
% 2.73/1.00  
% 2.73/1.00  --fof                                   false
% 2.73/1.00  --time_out_real                         305.
% 2.73/1.00  --time_out_virtual                      -1.
% 2.73/1.00  --symbol_type_check                     false
% 2.73/1.00  --clausify_out                          false
% 2.73/1.00  --sig_cnt_out                           false
% 2.73/1.00  --trig_cnt_out                          false
% 2.73/1.00  --trig_cnt_out_tolerance                1.
% 2.73/1.00  --trig_cnt_out_sk_spl                   false
% 2.73/1.00  --abstr_cl_out                          false
% 2.73/1.00  
% 2.73/1.00  ------ Global Options
% 2.73/1.00  
% 2.73/1.00  --schedule                              default
% 2.73/1.00  --add_important_lit                     false
% 2.73/1.00  --prop_solver_per_cl                    1000
% 2.73/1.00  --min_unsat_core                        false
% 2.73/1.00  --soft_assumptions                      false
% 2.73/1.00  --soft_lemma_size                       3
% 2.73/1.00  --prop_impl_unit_size                   0
% 2.73/1.00  --prop_impl_unit                        []
% 2.73/1.00  --share_sel_clauses                     true
% 2.73/1.00  --reset_solvers                         false
% 2.73/1.00  --bc_imp_inh                            [conj_cone]
% 2.73/1.00  --conj_cone_tolerance                   3.
% 2.73/1.00  --extra_neg_conj                        none
% 2.73/1.00  --large_theory_mode                     true
% 2.73/1.00  --prolific_symb_bound                   200
% 2.73/1.00  --lt_threshold                          2000
% 2.73/1.00  --clause_weak_htbl                      true
% 2.73/1.00  --gc_record_bc_elim                     false
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing Options
% 2.73/1.00  
% 2.73/1.00  --preprocessing_flag                    true
% 2.73/1.00  --time_out_prep_mult                    0.1
% 2.73/1.00  --splitting_mode                        input
% 2.73/1.00  --splitting_grd                         true
% 2.73/1.00  --splitting_cvd                         false
% 2.73/1.00  --splitting_cvd_svl                     false
% 2.73/1.00  --splitting_nvd                         32
% 2.73/1.00  --sub_typing                            true
% 2.73/1.00  --prep_gs_sim                           true
% 2.73/1.00  --prep_unflatten                        true
% 2.73/1.00  --prep_res_sim                          true
% 2.73/1.00  --prep_upred                            true
% 2.73/1.00  --prep_sem_filter                       exhaustive
% 2.73/1.00  --prep_sem_filter_out                   false
% 2.73/1.00  --pred_elim                             true
% 2.73/1.00  --res_sim_input                         true
% 2.73/1.00  --eq_ax_congr_red                       true
% 2.73/1.00  --pure_diseq_elim                       true
% 2.73/1.00  --brand_transform                       false
% 2.73/1.00  --non_eq_to_eq                          false
% 2.73/1.00  --prep_def_merge                        true
% 2.73/1.00  --prep_def_merge_prop_impl              false
% 2.73/1.00  --prep_def_merge_mbd                    true
% 2.73/1.00  --prep_def_merge_tr_red                 false
% 2.73/1.00  --prep_def_merge_tr_cl                  false
% 2.73/1.00  --smt_preprocessing                     true
% 2.73/1.00  --smt_ac_axioms                         fast
% 2.73/1.00  --preprocessed_out                      false
% 2.73/1.00  --preprocessed_stats                    false
% 2.73/1.00  
% 2.73/1.00  ------ Abstraction refinement Options
% 2.73/1.00  
% 2.73/1.00  --abstr_ref                             []
% 2.73/1.00  --abstr_ref_prep                        false
% 2.73/1.00  --abstr_ref_until_sat                   false
% 2.73/1.00  --abstr_ref_sig_restrict                funpre
% 2.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.00  --abstr_ref_under                       []
% 2.73/1.00  
% 2.73/1.00  ------ SAT Options
% 2.73/1.00  
% 2.73/1.00  --sat_mode                              false
% 2.73/1.00  --sat_fm_restart_options                ""
% 2.73/1.00  --sat_gr_def                            false
% 2.73/1.00  --sat_epr_types                         true
% 2.73/1.00  --sat_non_cyclic_types                  false
% 2.73/1.00  --sat_finite_models                     false
% 2.73/1.00  --sat_fm_lemmas                         false
% 2.73/1.00  --sat_fm_prep                           false
% 2.73/1.00  --sat_fm_uc_incr                        true
% 2.73/1.00  --sat_out_model                         small
% 2.73/1.00  --sat_out_clauses                       false
% 2.73/1.00  
% 2.73/1.00  ------ QBF Options
% 2.73/1.00  
% 2.73/1.00  --qbf_mode                              false
% 2.73/1.00  --qbf_elim_univ                         false
% 2.73/1.00  --qbf_dom_inst                          none
% 2.73/1.00  --qbf_dom_pre_inst                      false
% 2.73/1.00  --qbf_sk_in                             false
% 2.73/1.00  --qbf_pred_elim                         true
% 2.73/1.00  --qbf_split                             512
% 2.73/1.00  
% 2.73/1.00  ------ BMC1 Options
% 2.73/1.00  
% 2.73/1.00  --bmc1_incremental                      false
% 2.73/1.00  --bmc1_axioms                           reachable_all
% 2.73/1.00  --bmc1_min_bound                        0
% 2.73/1.00  --bmc1_max_bound                        -1
% 2.73/1.00  --bmc1_max_bound_default                -1
% 2.73/1.00  --bmc1_symbol_reachability              true
% 2.73/1.00  --bmc1_property_lemmas                  false
% 2.73/1.00  --bmc1_k_induction                      false
% 2.73/1.00  --bmc1_non_equiv_states                 false
% 2.73/1.00  --bmc1_deadlock                         false
% 2.73/1.00  --bmc1_ucm                              false
% 2.73/1.00  --bmc1_add_unsat_core                   none
% 2.73/1.00  --bmc1_unsat_core_children              false
% 2.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.00  --bmc1_out_stat                         full
% 2.73/1.00  --bmc1_ground_init                      false
% 2.73/1.00  --bmc1_pre_inst_next_state              false
% 2.73/1.00  --bmc1_pre_inst_state                   false
% 2.73/1.00  --bmc1_pre_inst_reach_state             false
% 2.73/1.00  --bmc1_out_unsat_core                   false
% 2.73/1.00  --bmc1_aig_witness_out                  false
% 2.73/1.00  --bmc1_verbose                          false
% 2.73/1.00  --bmc1_dump_clauses_tptp                false
% 2.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.00  --bmc1_dump_file                        -
% 2.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.00  --bmc1_ucm_extend_mode                  1
% 2.73/1.00  --bmc1_ucm_init_mode                    2
% 2.73/1.00  --bmc1_ucm_cone_mode                    none
% 2.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.00  --bmc1_ucm_relax_model                  4
% 2.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.00  --bmc1_ucm_layered_model                none
% 2.73/1.00  --bmc1_ucm_max_lemma_size               10
% 2.73/1.00  
% 2.73/1.00  ------ AIG Options
% 2.73/1.00  
% 2.73/1.00  --aig_mode                              false
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation Options
% 2.73/1.00  
% 2.73/1.00  --instantiation_flag                    true
% 2.73/1.00  --inst_sos_flag                         false
% 2.73/1.00  --inst_sos_phase                        true
% 2.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.00  --inst_lit_sel_side                     none
% 2.73/1.00  --inst_solver_per_active                1400
% 2.73/1.00  --inst_solver_calls_frac                1.
% 2.73/1.00  --inst_passive_queue_type               priority_queues
% 2.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.00  --inst_passive_queues_freq              [25;2]
% 2.73/1.00  --inst_dismatching                      true
% 2.73/1.00  --inst_eager_unprocessed_to_passive     true
% 2.73/1.00  --inst_prop_sim_given                   true
% 2.73/1.00  --inst_prop_sim_new                     false
% 2.73/1.00  --inst_subs_new                         false
% 2.73/1.00  --inst_eq_res_simp                      false
% 2.73/1.00  --inst_subs_given                       false
% 2.73/1.00  --inst_orphan_elimination               true
% 2.73/1.00  --inst_learning_loop_flag               true
% 2.73/1.00  --inst_learning_start                   3000
% 2.73/1.00  --inst_learning_factor                  2
% 2.73/1.00  --inst_start_prop_sim_after_learn       3
% 2.73/1.00  --inst_sel_renew                        solver
% 2.73/1.00  --inst_lit_activity_flag                true
% 2.73/1.00  --inst_restr_to_given                   false
% 2.73/1.00  --inst_activity_threshold               500
% 2.73/1.00  --inst_out_proof                        true
% 2.73/1.00  
% 2.73/1.00  ------ Resolution Options
% 2.73/1.00  
% 2.73/1.00  --resolution_flag                       false
% 2.73/1.00  --res_lit_sel                           adaptive
% 2.73/1.00  --res_lit_sel_side                      none
% 2.73/1.00  --res_ordering                          kbo
% 2.73/1.00  --res_to_prop_solver                    active
% 2.73/1.00  --res_prop_simpl_new                    false
% 2.73/1.00  --res_prop_simpl_given                  true
% 2.73/1.00  --res_passive_queue_type                priority_queues
% 2.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.00  --res_passive_queues_freq               [15;5]
% 2.73/1.00  --res_forward_subs                      full
% 2.73/1.00  --res_backward_subs                     full
% 2.73/1.00  --res_forward_subs_resolution           true
% 2.73/1.00  --res_backward_subs_resolution          true
% 2.73/1.00  --res_orphan_elimination                true
% 2.73/1.00  --res_time_limit                        2.
% 2.73/1.00  --res_out_proof                         true
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Options
% 2.73/1.00  
% 2.73/1.00  --superposition_flag                    true
% 2.73/1.00  --sup_passive_queue_type                priority_queues
% 2.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.00  --demod_completeness_check              fast
% 2.73/1.00  --demod_use_ground                      true
% 2.73/1.00  --sup_to_prop_solver                    passive
% 2.73/1.00  --sup_prop_simpl_new                    true
% 2.73/1.00  --sup_prop_simpl_given                  true
% 2.73/1.00  --sup_fun_splitting                     false
% 2.73/1.00  --sup_smt_interval                      50000
% 2.73/1.00  
% 2.73/1.00  ------ Superposition Simplification Setup
% 2.73/1.00  
% 2.73/1.00  --sup_indices_passive                   []
% 2.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_full_bw                           [BwDemod]
% 2.73/1.00  --sup_immed_triv                        [TrivRules]
% 2.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_immed_bw_main                     []
% 2.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.00  
% 2.73/1.00  ------ Combination Options
% 2.73/1.00  
% 2.73/1.00  --comb_res_mult                         3
% 2.73/1.00  --comb_sup_mult                         2
% 2.73/1.00  --comb_inst_mult                        10
% 2.73/1.00  
% 2.73/1.00  ------ Debug Options
% 2.73/1.00  
% 2.73/1.00  --dbg_backtrace                         false
% 2.73/1.00  --dbg_dump_prop_clauses                 false
% 2.73/1.00  --dbg_dump_prop_clauses_file            -
% 2.73/1.00  --dbg_out_stat                          false
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  ------ Proving...
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS status Theorem for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  fof(f3,axiom,(
% 2.73/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f12,plain,(
% 2.73/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.73/1.00    inference(ennf_transformation,[],[f3])).
% 2.73/1.00  
% 2.73/1.00  fof(f25,plain,(
% 2.73/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.73/1.00    inference(nnf_transformation,[],[f12])).
% 2.73/1.00  
% 2.73/1.00  fof(f39,plain,(
% 2.73/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f25])).
% 2.73/1.00  
% 2.73/1.00  fof(f7,conjecture,(
% 2.73/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f8,negated_conjecture,(
% 2.73/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 2.73/1.00    inference(negated_conjecture,[],[f7])).
% 2.73/1.00  
% 2.73/1.00  fof(f9,plain,(
% 2.73/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 2.73/1.00    inference(rectify,[],[f8])).
% 2.73/1.00  
% 2.73/1.00  fof(f10,plain,(
% 2.73/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 2.73/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.73/1.00  
% 2.73/1.00  fof(f18,plain,(
% 2.73/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.73/1.00    inference(ennf_transformation,[],[f10])).
% 2.73/1.00  
% 2.73/1.00  fof(f19,plain,(
% 2.73/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/1.00    inference(flattening,[],[f18])).
% 2.73/1.00  
% 2.73/1.00  fof(f30,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) => (! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))))) )),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f29,plain,(
% 2.73/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3)))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f28,plain,(
% 2.73/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f27,plain,(
% 2.73/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2)))) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f31,plain,(
% 2.73/1.00    (((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f30,f29,f28,f27])).
% 2.73/1.00  
% 2.73/1.00  fof(f55,plain,(
% 2.73/1.00    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f54,plain,(
% 2.73/1.00    m1_pre_topc(sK3,sK1)),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f52,plain,(
% 2.73/1.00    m1_pre_topc(sK2,sK1)),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f5,axiom,(
% 2.73/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f14,plain,(
% 2.73/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/1.00    inference(ennf_transformation,[],[f5])).
% 2.73/1.00  
% 2.73/1.00  fof(f15,plain,(
% 2.73/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/1.00    inference(flattening,[],[f14])).
% 2.73/1.00  
% 2.73/1.00  fof(f26,plain,(
% 2.73/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/1.00    inference(nnf_transformation,[],[f15])).
% 2.73/1.00  
% 2.73/1.00  fof(f44,plain,(
% 2.73/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f26])).
% 2.73/1.00  
% 2.73/1.00  fof(f61,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/1.00    inference(equality_resolution,[],[f44])).
% 2.73/1.00  
% 2.73/1.00  fof(f6,axiom,(
% 2.73/1.00    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f16,plain,(
% 2.73/1.00    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/1.00    inference(ennf_transformation,[],[f6])).
% 2.73/1.00  
% 2.73/1.00  fof(f17,plain,(
% 2.73/1.00    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/1.00    inference(flattening,[],[f16])).
% 2.73/1.00  
% 2.73/1.00  fof(f46,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f17])).
% 2.73/1.00  
% 2.73/1.00  fof(f47,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f17])).
% 2.73/1.00  
% 2.73/1.00  fof(f48,plain,(
% 2.73/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f17])).
% 2.73/1.00  
% 2.73/1.00  fof(f50,plain,(
% 2.73/1.00    l1_pre_topc(sK1)),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f49,plain,(
% 2.73/1.00    ~v2_struct_0(sK1)),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f51,plain,(
% 2.73/1.00    ~v2_struct_0(sK2)),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f53,plain,(
% 2.73/1.00    ~v2_struct_0(sK3)),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f1,axiom,(
% 2.73/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f20,plain,(
% 2.73/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.73/1.00    inference(nnf_transformation,[],[f1])).
% 2.73/1.00  
% 2.73/1.00  fof(f21,plain,(
% 2.73/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.73/1.00    inference(flattening,[],[f20])).
% 2.73/1.00  
% 2.73/1.00  fof(f22,plain,(
% 2.73/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.73/1.00    inference(rectify,[],[f21])).
% 2.73/1.00  
% 2.73/1.00  fof(f23,plain,(
% 2.73/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.73/1.00    introduced(choice_axiom,[])).
% 2.73/1.00  
% 2.73/1.00  fof(f24,plain,(
% 2.73/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.73/1.00  
% 2.73/1.00  fof(f32,plain,(
% 2.73/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.73/1.00    inference(cnf_transformation,[],[f24])).
% 2.73/1.00  
% 2.73/1.00  fof(f60,plain,(
% 2.73/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 2.73/1.00    inference(equality_resolution,[],[f32])).
% 2.73/1.00  
% 2.73/1.00  fof(f2,axiom,(
% 2.73/1.00    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f11,plain,(
% 2.73/1.00    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0))),
% 2.73/1.00    inference(ennf_transformation,[],[f2])).
% 2.73/1.00  
% 2.73/1.00  fof(f38,plain,(
% 2.73/1.00    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f11])).
% 2.73/1.00  
% 2.73/1.00  fof(f42,plain,(
% 2.73/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f25])).
% 2.73/1.00  
% 2.73/1.00  fof(f57,plain,(
% 2.73/1.00    ( ! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f62,plain,(
% 2.73/1.00    ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.73/1.00    inference(equality_resolution,[],[f57])).
% 2.73/1.00  
% 2.73/1.00  fof(f41,plain,(
% 2.73/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f25])).
% 2.73/1.00  
% 2.73/1.00  fof(f40,plain,(
% 2.73/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f25])).
% 2.73/1.00  
% 2.73/1.00  fof(f4,axiom,(
% 2.73/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/1.00  
% 2.73/1.00  fof(f13,plain,(
% 2.73/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.73/1.00    inference(ennf_transformation,[],[f4])).
% 2.73/1.00  
% 2.73/1.00  fof(f43,plain,(
% 2.73/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.73/1.00    inference(cnf_transformation,[],[f13])).
% 2.73/1.00  
% 2.73/1.00  fof(f56,plain,(
% 2.73/1.00    ( ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 2.73/1.00    inference(cnf_transformation,[],[f31])).
% 2.73/1.00  
% 2.73/1.00  fof(f63,plain,(
% 2.73/1.00    ~m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.73/1.00    inference(equality_resolution,[],[f56])).
% 2.73/1.00  
% 2.73/1.00  cnf(c_10,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_19,negated_conjecture,
% 2.73/1.00      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 2.73/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_388,plain,
% 2.73/1.00      ( r2_hidden(X0,X1)
% 2.73/1.00      | v1_xboole_0(X1)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) != X1
% 2.73/1.00      | sK4 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_389,plain,
% 2.73/1.00      ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_388]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1114,plain,
% 2.73/1.00      ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_20,negated_conjecture,
% 2.73/1.00      ( m1_pre_topc(sK3,sK1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1124,plain,
% 2.73/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_22,negated_conjecture,
% 2.73/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1122,plain,
% 2.73/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_13,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_pre_topc(X2,X1)
% 2.73/1.00      | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X2)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(k1_tsep_1(X1,X2,X0))
% 2.73/1.00      | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
% 2.73/1.00      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_16,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_pre_topc(X2,X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X2)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_15,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_pre_topc(X2,X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X2)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_14,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_pre_topc(X2,X1)
% 2.73/1.00      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X2)
% 2.73/1.00      | v2_struct_0(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_143,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X2,X1)
% 2.73/1.00      | ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X2)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_13,c_16,c_15,c_14]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_144,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_pre_topc(X2,X1)
% 2.73/1.00      | ~ l1_pre_topc(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X2)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_143]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_24,negated_conjecture,
% 2.73/1.00      ( l1_pre_topc(sK1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_446,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.73/1.00      | ~ m1_pre_topc(X2,X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X2)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
% 2.73/1.00      | sK1 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_144,c_24]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_447,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,sK1)
% 2.73/1.00      | ~ m1_pre_topc(X1,sK1)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(sK1)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(sK1,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_446]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_25,negated_conjecture,
% 2.73/1.00      ( ~ v2_struct_0(sK1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_451,plain,
% 2.73/1.00      ( v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | ~ m1_pre_topc(X1,sK1)
% 2.73/1.00      | ~ m1_pre_topc(X0,sK1)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(sK1,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_447,c_25]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_452,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,sK1)
% 2.73/1.00      | ~ m1_pre_topc(X1,sK1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(X1)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(sK1,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_451]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1112,plain,
% 2.73/1.00      ( u1_struct_0(k1_tsep_1(sK1,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 2.73/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.73/1.00      | m1_pre_topc(X1,sK1) != iProver_top
% 2.73/1.00      | v2_struct_0(X1) = iProver_top
% 2.73/1.00      | v2_struct_0(X0) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2293,plain,
% 2.73/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
% 2.73/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.73/1.00      | v2_struct_0(X0) = iProver_top
% 2.73/1.00      | v2_struct_0(sK2) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1122,c_1112]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_23,negated_conjecture,
% 2.73/1.00      ( ~ v2_struct_0(sK2) ),
% 2.73/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_28,plain,
% 2.73/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3958,plain,
% 2.73/1.00      ( v2_struct_0(X0) = iProver_top
% 2.73/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.73/1.00      | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2293,c_28]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3959,plain,
% 2.73/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
% 2.73/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.73/1.00      | v2_struct_0(X0) = iProver_top ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_3958]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3967,plain,
% 2.73/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
% 2.73/1.00      | v2_struct_0(sK3) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1124,c_3959]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_21,negated_conjecture,
% 2.73/1.00      ( ~ v2_struct_0(sK3) ),
% 2.73/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1362,plain,
% 2.73/1.00      ( ~ m1_pre_topc(X0,sK1)
% 2.73/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.73/1.00      | v2_struct_0(X0)
% 2.73/1.00      | v2_struct_0(sK2)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_452]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1564,plain,
% 2.73/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.73/1.00      | ~ m1_pre_topc(sK3,sK1)
% 2.73/1.00      | v2_struct_0(sK2)
% 2.73/1.00      | v2_struct_0(sK3)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_1362]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4294,plain,
% 2.73/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_3967,c_23,c_22,c_21,c_20,c_1564]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5,plain,
% 2.73/1.00      ( r2_hidden(X0,X1)
% 2.73/1.00      | r2_hidden(X0,X2)
% 2.73/1.00      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1126,plain,
% 2.73/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.73/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.73/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4297,plain,
% 2.73/1.00      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.73/1.00      | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
% 2.73/1.00      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4294,c_1126]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_9331,plain,
% 2.73/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 2.73/1.00      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 2.73/1.00      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1114,c_4297]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_6,plain,
% 2.73/1.00      ( v1_xboole_0(X0) | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1125,plain,
% 2.73/1.00      ( v1_xboole_0(X0) = iProver_top
% 2.73/1.00      | v1_xboole_0(k2_xboole_0(X1,X0)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4300,plain,
% 2.73/1.00      ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.73/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4294,c_1125]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_7,plain,
% 2.73/1.00      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_17,negated_conjecture,
% 2.73/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_361,plain,
% 2.73/1.00      ( ~ v1_xboole_0(X0)
% 2.73/1.00      | ~ v1_xboole_0(X1)
% 2.73/1.00      | u1_struct_0(sK3) != X0
% 2.73/1.00      | sK4 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_362,plain,
% 2.73/1.00      ( ~ v1_xboole_0(u1_struct_0(sK3)) | ~ v1_xboole_0(sK4) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_361]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_363,plain,
% 2.73/1.00      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 2.73/1.00      | v1_xboole_0(sK4) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_8,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_398,plain,
% 2.73/1.00      ( ~ v1_xboole_0(X0)
% 2.73/1.00      | v1_xboole_0(X1)
% 2.73/1.00      | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) != X0
% 2.73/1.00      | sK4 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_399,plain,
% 2.73/1.00      ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
% 2.73/1.00      | v1_xboole_0(sK4) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_398]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_400,plain,
% 2.73/1.00      ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.73/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5738,plain,
% 2.73/1.00      ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_4300,c_363,c_400]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_9,plain,
% 2.73/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_11,plain,
% 2.73/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_153,plain,
% 2.73/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_9,c_11]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_154,plain,
% 2.73/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_153]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_18,negated_conjecture,
% 2.73/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_371,plain,
% 2.73/1.00      ( ~ r2_hidden(X0,X1) | u1_struct_0(sK2) != X1 | sK4 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_154,c_18]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_372,plain,
% 2.73/1.00      ( ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_371]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_373,plain,
% 2.73/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_354,plain,
% 2.73/1.00      ( ~ r2_hidden(X0,X1) | u1_struct_0(sK3) != X1 | sK4 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_154,c_17]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_355,plain,
% 2.73/1.00      ( ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_354]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_356,plain,
% 2.73/1.00      ( r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(contradiction,plain,
% 2.73/1.00      ( $false ),
% 2.73/1.00      inference(minisat,[status(thm)],[c_9331,c_5738,c_373,c_356]) ).
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  ------                               Statistics
% 2.73/1.00  
% 2.73/1.00  ------ General
% 2.73/1.00  
% 2.73/1.00  abstr_ref_over_cycles:                  0
% 2.73/1.00  abstr_ref_under_cycles:                 0
% 2.73/1.00  gc_basic_clause_elim:                   0
% 2.73/1.00  forced_gc_time:                         0
% 2.73/1.00  parsing_time:                           0.011
% 2.73/1.00  unif_index_cands_time:                  0.
% 2.73/1.00  unif_index_add_time:                    0.
% 2.73/1.00  orderings_time:                         0.
% 2.73/1.00  out_proof_time:                         0.009
% 2.73/1.00  total_time:                             0.385
% 2.73/1.00  num_of_symbols:                         46
% 2.73/1.00  num_of_terms:                           9174
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing
% 2.73/1.00  
% 2.73/1.00  num_of_splits:                          0
% 2.73/1.00  num_of_split_atoms:                     0
% 2.73/1.00  num_of_reused_defs:                     0
% 2.73/1.00  num_eq_ax_congr_red:                    6
% 2.73/1.00  num_of_sem_filtered_clauses:            1
% 2.73/1.00  num_of_subtypes:                        0
% 2.73/1.00  monotx_restored_types:                  0
% 2.73/1.00  sat_num_of_epr_types:                   0
% 2.73/1.00  sat_num_of_non_cyclic_types:            0
% 2.73/1.00  sat_guarded_non_collapsed_types:        0
% 2.73/1.00  num_pure_diseq_elim:                    0
% 2.73/1.00  simp_replaced_by:                       0
% 2.73/1.00  res_preprocessed:                       98
% 2.73/1.00  prep_upred:                             0
% 2.73/1.00  prep_unflattend:                        19
% 2.73/1.00  smt_new_axioms:                         0
% 2.73/1.00  pred_elim_cands:                        7
% 2.73/1.00  pred_elim:                              2
% 2.73/1.00  pred_elim_cl:                           -1
% 2.73/1.00  pred_elim_cycles:                       4
% 2.73/1.00  merged_defs:                            0
% 2.73/1.00  merged_defs_ncl:                        0
% 2.73/1.00  bin_hyper_res:                          0
% 2.73/1.00  prep_cycles:                            3
% 2.73/1.00  pred_elim_time:                         0.009
% 2.73/1.00  splitting_time:                         0.
% 2.73/1.00  sem_filter_time:                        0.
% 2.73/1.00  monotx_time:                            0.001
% 2.73/1.00  subtype_inf_time:                       0.
% 2.73/1.00  
% 2.73/1.00  ------ Problem properties
% 2.73/1.00  
% 2.73/1.00  clauses:                                26
% 2.73/1.00  conjectures:                            5
% 2.73/1.00  epr:                                    6
% 2.73/1.00  horn:                                   18
% 2.73/1.00  ground:                                 13
% 2.73/1.00  unary:                                  7
% 2.73/1.00  binary:                                 9
% 2.73/1.00  lits:                                   70
% 2.73/1.00  lits_eq:                                10
% 2.73/1.00  fd_pure:                                0
% 2.73/1.00  fd_pseudo:                              0
% 2.73/1.00  fd_cond:                                0
% 2.73/1.00  fd_pseudo_cond:                         4
% 2.73/1.00  ac_symbols:                             0
% 2.73/1.00  
% 2.73/1.00  ------ Propositional Solver
% 2.73/1.00  
% 2.73/1.00  prop_solver_calls:                      23
% 2.73/1.00  prop_fast_solver_calls:                 1060
% 2.73/1.00  smt_solver_calls:                       0
% 2.73/1.00  smt_fast_solver_calls:                  0
% 2.73/1.00  prop_num_of_clauses:                    3876
% 2.73/1.00  prop_preprocess_simplified:             7570
% 2.73/1.00  prop_fo_subsumed:                       52
% 2.73/1.00  prop_solver_time:                       0.
% 2.73/1.00  smt_solver_time:                        0.
% 2.73/1.00  smt_fast_solver_time:                   0.
% 2.73/1.00  prop_fast_solver_time:                  0.
% 2.73/1.00  prop_unsat_core_time:                   0.
% 2.73/1.00  
% 2.73/1.00  ------ QBF
% 2.73/1.00  
% 2.73/1.00  qbf_q_res:                              0
% 2.73/1.00  qbf_num_tautologies:                    0
% 2.73/1.00  qbf_prep_cycles:                        0
% 2.73/1.00  
% 2.73/1.00  ------ BMC1
% 2.73/1.00  
% 2.73/1.00  bmc1_current_bound:                     -1
% 2.73/1.00  bmc1_last_solved_bound:                 -1
% 2.73/1.00  bmc1_unsat_core_size:                   -1
% 2.73/1.00  bmc1_unsat_core_parents_size:           -1
% 2.73/1.00  bmc1_merge_next_fun:                    0
% 2.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation
% 2.73/1.00  
% 2.73/1.00  inst_num_of_clauses:                    890
% 2.73/1.00  inst_num_in_passive:                    259
% 2.73/1.00  inst_num_in_active:                     486
% 2.73/1.00  inst_num_in_unprocessed:                147
% 2.73/1.00  inst_num_of_loops:                      560
% 2.73/1.00  inst_num_of_learning_restarts:          0
% 2.73/1.00  inst_num_moves_active_passive:          72
% 2.73/1.00  inst_lit_activity:                      0
% 2.73/1.00  inst_lit_activity_moves:                1
% 2.73/1.00  inst_num_tautologies:                   0
% 2.73/1.00  inst_num_prop_implied:                  0
% 2.73/1.00  inst_num_existing_simplified:           0
% 2.73/1.00  inst_num_eq_res_simplified:             0
% 2.73/1.00  inst_num_child_elim:                    0
% 2.73/1.00  inst_num_of_dismatching_blockings:      496
% 2.73/1.00  inst_num_of_non_proper_insts:           600
% 2.73/1.00  inst_num_of_duplicates:                 0
% 2.73/1.00  inst_inst_num_from_inst_to_res:         0
% 2.73/1.00  inst_dismatching_checking_time:         0.
% 2.73/1.00  
% 2.73/1.00  ------ Resolution
% 2.73/1.00  
% 2.73/1.00  res_num_of_clauses:                     0
% 2.73/1.00  res_num_in_passive:                     0
% 2.73/1.00  res_num_in_active:                      0
% 2.73/1.00  res_num_of_loops:                       101
% 2.73/1.00  res_forward_subset_subsumed:            6
% 2.73/1.00  res_backward_subset_subsumed:           4
% 2.73/1.00  res_forward_subsumed:                   0
% 2.73/1.00  res_backward_subsumed:                  0
% 2.73/1.00  res_forward_subsumption_resolution:     3
% 2.73/1.00  res_backward_subsumption_resolution:    0
% 2.73/1.00  res_clause_to_clause_subsumption:       1022
% 2.73/1.00  res_orphan_elimination:                 0
% 2.73/1.00  res_tautology_del:                      13
% 2.73/1.00  res_num_eq_res_simplified:              2
% 2.73/1.00  res_num_sel_changes:                    0
% 2.73/1.00  res_moves_from_active_to_pass:          0
% 2.73/1.00  
% 2.73/1.00  ------ Superposition
% 2.73/1.00  
% 2.73/1.00  sup_time_total:                         0.
% 2.73/1.00  sup_time_generating:                    0.
% 2.73/1.00  sup_time_sim_full:                      0.
% 2.73/1.00  sup_time_sim_immed:                     0.
% 2.73/1.00  
% 2.73/1.00  sup_num_of_clauses:                     292
% 2.73/1.00  sup_num_in_active:                      111
% 2.73/1.00  sup_num_in_passive:                     181
% 2.73/1.00  sup_num_of_loops:                       111
% 2.73/1.00  sup_fw_superposition:                   109
% 2.73/1.00  sup_bw_superposition:                   200
% 2.73/1.00  sup_immediate_simplified:               2
% 2.73/1.00  sup_given_eliminated:                   0
% 2.73/1.00  comparisons_done:                       0
% 2.73/1.00  comparisons_avoided:                    0
% 2.73/1.00  
% 2.73/1.00  ------ Simplifications
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  sim_fw_subset_subsumed:                 5
% 2.73/1.00  sim_bw_subset_subsumed:                 1
% 2.73/1.00  sim_fw_subsumed:                        0
% 2.73/1.00  sim_bw_subsumed:                        0
% 2.73/1.00  sim_fw_subsumption_res:                 0
% 2.73/1.00  sim_bw_subsumption_res:                 0
% 2.73/1.00  sim_tautology_del:                      14
% 2.73/1.00  sim_eq_tautology_del:                   0
% 2.73/1.00  sim_eq_res_simp:                        8
% 2.73/1.00  sim_fw_demodulated:                     0
% 2.73/1.00  sim_bw_demodulated:                     0
% 2.73/1.00  sim_light_normalised:                   0
% 2.73/1.00  sim_joinable_taut:                      0
% 2.73/1.00  sim_joinable_simp:                      0
% 2.73/1.00  sim_ac_normalised:                      0
% 2.73/1.00  sim_smt_subsumption:                    0
% 2.73/1.00  
%------------------------------------------------------------------------------

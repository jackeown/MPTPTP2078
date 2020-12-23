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
% DateTime   : Thu Dec  3 12:21:47 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  141 (6464 expanded)
%              Number of clauses        :   83 (1229 expanded)
%              Number of leaves         :   12 (1929 expanded)
%              Depth                    :   26
%              Number of atoms          :  610 (63290 expanded)
%              Number of equality atoms :  178 (11999 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f11,plain,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f31,f30,f29,f28])).

fof(f53,plain,(
    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
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
    inference(equality_resolution,[],[f42])).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f55,plain,(
    ! [X4] :
      ( sK4 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X5] :
      ( sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f54])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_617,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_624,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2187,plain,
    ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_624])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_614,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_616,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_188,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_13,c_12,c_11])).

cnf(c_189,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_610,plain,
    ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_1195,plain,
    ( u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_610])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1570,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1195,c_23,c_24,c_27])).

cnf(c_1571,plain,
    ( u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1570])).

cnf(c_1580,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_1571])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_911,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_1278,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_1659,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1580,c_22,c_21,c_20,c_19,c_18,c_17,c_1278])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_626,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2353,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_626])).

cnf(c_3022,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2187,c_2353])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_996,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_14,c_7])).

cnf(c_997,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1001,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_15,c_7])).

cnf(c_1002,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_4173,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3022,c_997,c_1002])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_629,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1196,plain,
    ( u1_struct_0(k1_tsep_1(sK1,X0,sK2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_610])).

cnf(c_25,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1751,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | u1_struct_0(k1_tsep_1(sK1,X0,sK2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1196,c_23,c_24,c_25])).

cnf(c_1752,plain,
    ( u1_struct_0(k1_tsep_1(sK1,X0,sK2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1751])).

cnf(c_1760,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1752])).

cnf(c_916,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK1,X0,sK2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_1293,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | u1_struct_0(k1_tsep_1(sK1,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_1773,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1760,c_22,c_21,c_20,c_19,c_18,c_17,c_1293])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_628,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2155,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK3,sK2))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_628])).

cnf(c_2354,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK3,sK2))) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_626])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_627,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1662,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_627])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_632,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2046,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_632])).

cnf(c_2154,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_628])).

cnf(c_2723,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2154,c_632])).

cnf(c_4461,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK3,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2354,c_997,c_1002,c_2046,c_2723,c_3022])).

cnf(c_4471,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_4461])).

cnf(c_6406,plain,
    ( k2_xboole_0(X0,u1_struct_0(sK2)) = X1
    | r2_hidden(sK0(X0,u1_struct_0(sK2),X1),X1) = iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK2),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_4471])).

cnf(c_6649,plain,
    ( k2_xboole_0(X0,u1_struct_0(sK2)) = X1
    | r2_hidden(sK0(X0,u1_struct_0(sK2),X1),X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6406,c_632])).

cnf(c_7206,plain,
    ( k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6649,c_4471])).

cnf(c_1761,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_1752])).

cnf(c_1296,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_1889,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1761,c_22,c_21,c_20,c_19,c_1296])).

cnf(c_7221,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7206,c_1889])).

cnf(c_7291,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_4173,c_7221])).

cnf(c_6646,plain,
    ( k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = X0
    | r2_hidden(sK0(u1_struct_0(sK2),u1_struct_0(sK2),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6406,c_4471])).

cnf(c_6731,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = X0
    | r2_hidden(sK0(u1_struct_0(sK2),u1_struct_0(sK2),X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6646,c_1889])).

cnf(c_1776,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK3,sK2))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_627])).

cnf(c_4472,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_4461])).

cnf(c_7421,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_6731,c_4472])).

cnf(c_8875,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = u1_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7291,c_7421])).

cnf(c_8884,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8875,c_617])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8884,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.54/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/1.00  
% 3.54/1.00  ------  iProver source info
% 3.54/1.00  
% 3.54/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.54/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/1.00  git: non_committed_changes: false
% 3.54/1.00  git: last_make_outside_of_git: false
% 3.54/1.00  
% 3.54/1.00  ------ 
% 3.54/1.00  ------ Parsing...
% 3.54/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.00  ------ Proving...
% 3.54/1.00  ------ Problem Properties 
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  clauses                                 23
% 3.54/1.00  conjectures                             9
% 3.54/1.00  EPR                                     9
% 3.54/1.00  Horn                                    15
% 3.54/1.00  unary                                   9
% 3.54/1.00  binary                                  4
% 3.54/1.00  lits                                    72
% 3.54/1.00  lits eq                                 6
% 3.54/1.00  fd_pure                                 0
% 3.54/1.00  fd_pseudo                               0
% 3.54/1.00  fd_cond                                 0
% 3.54/1.00  fd_pseudo_cond                          4
% 3.54/1.00  AC symbols                              0
% 3.54/1.00  
% 3.54/1.00  ------ Input Options Time Limit: Unbounded
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  ------ 
% 3.54/1.00  Current options:
% 3.54/1.00  ------ 
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  ------ Proving...
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  % SZS status Theorem for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  fof(f7,conjecture,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f8,negated_conjecture,(
% 3.54/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 3.54/1.00    inference(negated_conjecture,[],[f7])).
% 3.54/1.00  
% 3.54/1.00  fof(f9,plain,(
% 3.54/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 3.54/1.00    inference(rectify,[],[f8])).
% 3.54/1.00  
% 3.54/1.00  fof(f11,plain,(
% 3.54/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 3.54/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.54/1.00  
% 3.54/1.00  fof(f20,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f11])).
% 3.54/1.00  
% 3.54/1.00  fof(f21,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f20])).
% 3.54/1.00  
% 3.54/1.00  fof(f31,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) => (! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f30,plain,(
% 3.54/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3)))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f29,plain,(
% 3.54/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f28,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2)))) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f32,plain,(
% 3.54/1.00    (((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.54/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f31,f30,f29,f28])).
% 3.54/1.00  
% 3.54/1.00  fof(f53,plain,(
% 3.54/1.00    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f4,axiom,(
% 3.54/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f14,plain,(
% 3.54/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.54/1.00    inference(ennf_transformation,[],[f4])).
% 3.54/1.00  
% 3.54/1.00  fof(f15,plain,(
% 3.54/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.54/1.00    inference(flattening,[],[f14])).
% 3.54/1.00  
% 3.54/1.00  fof(f41,plain,(
% 3.54/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f15])).
% 3.54/1.00  
% 3.54/1.00  fof(f50,plain,(
% 3.54/1.00    m1_pre_topc(sK2,sK1)),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f52,plain,(
% 3.54/1.00    m1_pre_topc(sK3,sK1)),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f5,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f16,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f5])).
% 3.54/1.00  
% 3.54/1.00  fof(f17,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f16])).
% 3.54/1.00  
% 3.54/1.00  fof(f27,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(nnf_transformation,[],[f17])).
% 3.54/1.00  
% 3.54/1.00  fof(f42,plain,(
% 3.54/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f27])).
% 3.54/1.00  
% 3.54/1.00  fof(f59,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(equality_resolution,[],[f42])).
% 3.54/1.00  
% 3.54/1.00  fof(f6,axiom,(
% 3.54/1.00    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f18,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f6])).
% 3.54/1.00  
% 3.54/1.00  fof(f19,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f18])).
% 3.54/1.00  
% 3.54/1.00  fof(f44,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f19])).
% 3.54/1.00  
% 3.54/1.00  fof(f45,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f19])).
% 3.54/1.00  
% 3.54/1.00  fof(f46,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f19])).
% 3.54/1.00  
% 3.54/1.00  fof(f47,plain,(
% 3.54/1.00    ~v2_struct_0(sK1)),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f48,plain,(
% 3.54/1.00    l1_pre_topc(sK1)),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f51,plain,(
% 3.54/1.00    ~v2_struct_0(sK3)),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f49,plain,(
% 3.54/1.00    ~v2_struct_0(sK2)),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f2,axiom,(
% 3.54/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f22,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.54/1.00    inference(nnf_transformation,[],[f2])).
% 3.54/1.00  
% 3.54/1.00  fof(f23,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.54/1.00    inference(flattening,[],[f22])).
% 3.54/1.00  
% 3.54/1.00  fof(f24,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.54/1.00    inference(rectify,[],[f23])).
% 3.54/1.00  
% 3.54/1.00  fof(f25,plain,(
% 3.54/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f26,plain,(
% 3.54/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.54/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.54/1.00  
% 3.54/1.00  fof(f34,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.54/1.00    inference(cnf_transformation,[],[f26])).
% 3.54/1.00  
% 3.54/1.00  fof(f58,plain,(
% 3.54/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.54/1.00    inference(equality_resolution,[],[f34])).
% 3.54/1.00  
% 3.54/1.00  fof(f55,plain,(
% 3.54/1.00    ( ! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) )),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f60,plain,(
% 3.54/1.00    ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.54/1.00    inference(equality_resolution,[],[f55])).
% 3.54/1.00  
% 3.54/1.00  fof(f3,axiom,(
% 3.54/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f13,plain,(
% 3.54/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.54/1.00    inference(ennf_transformation,[],[f3])).
% 3.54/1.00  
% 3.54/1.00  fof(f40,plain,(
% 3.54/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f13])).
% 3.54/1.00  
% 3.54/1.00  fof(f54,plain,(
% 3.54/1.00    ( ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 3.54/1.00    inference(cnf_transformation,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f61,plain,(
% 3.54/1.00    ~m1_subset_1(sK4,u1_struct_0(sK2))),
% 3.54/1.00    inference(equality_resolution,[],[f54])).
% 3.54/1.00  
% 3.54/1.00  fof(f37,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f26])).
% 3.54/1.00  
% 3.54/1.00  fof(f36,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.54/1.00    inference(cnf_transformation,[],[f26])).
% 3.54/1.00  
% 3.54/1.00  fof(f56,plain,(
% 3.54/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.54/1.00    inference(equality_resolution,[],[f36])).
% 3.54/1.00  
% 3.54/1.00  fof(f35,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.54/1.00    inference(cnf_transformation,[],[f26])).
% 3.54/1.00  
% 3.54/1.00  fof(f57,plain,(
% 3.54/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.54/1.00    inference(equality_resolution,[],[f35])).
% 3.54/1.00  
% 3.54/1.00  fof(f1,axiom,(
% 3.54/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f10,plain,(
% 3.54/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.54/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.54/1.00  
% 3.54/1.00  fof(f12,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f10])).
% 3.54/1.00  
% 3.54/1.00  fof(f33,plain,(
% 3.54/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f12])).
% 3.54/1.00  
% 3.54/1.00  cnf(c_16,negated_conjecture,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 3.54/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_617,plain,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_624,plain,
% 3.54/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.54/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.54/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2187,plain,
% 3.54/1.00      ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_617,c_624]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_19,negated_conjecture,
% 3.54/1.00      ( m1_pre_topc(sK2,sK1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_614,plain,
% 3.54/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_17,negated_conjecture,
% 3.54/1.00      ( m1_pre_topc(sK3,sK1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_616,plain,
% 3.54/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X2,X1)
% 3.54/1.00      | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v2_struct_0(k1_tsep_1(X1,X2,X0))
% 3.54/1.00      | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
% 3.54/1.00      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_13,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X2,X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_12,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X2,X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v1_pre_topc(k1_tsep_1(X1,X2,X0)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_11,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X2,X1)
% 3.54/1.00      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_188,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X2,X1)
% 3.54/1.00      | ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_10,c_13,c_12,c_11]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_189,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X2,X1)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_188]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_610,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
% 3.54/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(X2) = iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1195,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
% 3.54/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(sK1) = iProver_top
% 3.54/1.00      | v2_struct_0(sK3) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_616,c_610]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_22,negated_conjecture,
% 3.54/1.00      ( ~ v2_struct_0(sK1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_23,plain,
% 3.54/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_21,negated_conjecture,
% 3.54/1.00      ( l1_pre_topc(sK1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_24,plain,
% 3.54/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_18,negated_conjecture,
% 3.54/1.00      ( ~ v2_struct_0(sK3) ),
% 3.54/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_27,plain,
% 3.54/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1570,plain,
% 3.54/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.54/1.00      | u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
% 3.54/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_1195,c_23,c_24,c_27]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1571,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
% 3.54/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_1570]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1580,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.54/1.00      | v2_struct_0(sK2) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_614,c_1571]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_20,negated_conjecture,
% 3.54/1.00      ( ~ v2_struct_0(sK2) ),
% 3.54/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_911,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,sK1)
% 3.54/1.00      | ~ m1_pre_topc(sK3,sK1)
% 3.54/1.00      | ~ l1_pre_topc(sK1)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v2_struct_0(sK1)
% 3.54/1.00      | v2_struct_0(sK3)
% 3.54/1.00      | u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_189]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1278,plain,
% 3.54/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 3.54/1.00      | ~ m1_pre_topc(sK3,sK1)
% 3.54/1.00      | ~ l1_pre_topc(sK1)
% 3.54/1.00      | v2_struct_0(sK1)
% 3.54/1.00      | v2_struct_0(sK2)
% 3.54/1.00      | v2_struct_0(sK3)
% 3.54/1.00      | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_911]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1659,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_1580,c_22,c_21,c_20,c_19,c_18,c_17,c_1278]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6,plain,
% 3.54/1.00      ( r2_hidden(X0,X1)
% 3.54/1.00      | r2_hidden(X0,X2)
% 3.54/1.00      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_626,plain,
% 3.54/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.54/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.54/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2353,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1659,c_626]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3022,plain,
% 3.54/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 3.54/1.00      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_2187,c_2353]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_14,negated_conjecture,
% 3.54/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7,plain,
% 3.54/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_996,plain,
% 3.54/1.00      ( ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
% 3.54/1.00      inference(resolution,[status(thm)],[c_14,c_7]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_997,plain,
% 3.54/1.00      ( r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_15,negated_conjecture,
% 3.54/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1001,plain,
% 3.54/1.00      ( ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 3.54/1.00      inference(resolution,[status(thm)],[c_15,c_7]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1002,plain,
% 3.54/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4173,plain,
% 3.54/1.00      ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_3022,c_997,c_1002]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3,plain,
% 3.54/1.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.54/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.54/1.00      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.54/1.00      | k2_xboole_0(X0,X1) = X2 ),
% 3.54/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_629,plain,
% 3.54/1.00      ( k2_xboole_0(X0,X1) = X2
% 3.54/1.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 3.54/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.54/1.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1196,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,X0,sK2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
% 3.54/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(sK1) = iProver_top
% 3.54/1.00      | v2_struct_0(sK2) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_614,c_610]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_25,plain,
% 3.54/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1751,plain,
% 3.54/1.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.54/1.00      | u1_struct_0(k1_tsep_1(sK1,X0,sK2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
% 3.54/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_1196,c_23,c_24,c_25]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1752,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,X0,sK2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
% 3.54/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_1751]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1760,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
% 3.54/1.00      | v2_struct_0(sK3) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_616,c_1752]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_916,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,sK1)
% 3.54/1.00      | ~ m1_pre_topc(sK2,sK1)
% 3.54/1.00      | ~ l1_pre_topc(sK1)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v2_struct_0(sK1)
% 3.54/1.00      | v2_struct_0(sK2)
% 3.54/1.00      | u1_struct_0(k1_tsep_1(sK1,X0,sK2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2)) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_189]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1293,plain,
% 3.54/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 3.54/1.00      | ~ m1_pre_topc(sK3,sK1)
% 3.54/1.00      | ~ l1_pre_topc(sK1)
% 3.54/1.00      | v2_struct_0(sK1)
% 3.54/1.00      | v2_struct_0(sK2)
% 3.54/1.00      | v2_struct_0(sK3)
% 3.54/1.00      | u1_struct_0(k1_tsep_1(sK1,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_916]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1773,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK3,sK2)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_1760,c_22,c_21,c_20,c_19,c_18,c_17,c_1293]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4,plain,
% 3.54/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_628,plain,
% 3.54/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.54/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2155,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK3,sK2))) = iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1773,c_628]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2354,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK3,sK2))) != iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1773,c_626]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5,plain,
% 3.54/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_627,plain,
% 3.54/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.54/1.00      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1662,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1659,c_627]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_0,plain,
% 3.54/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_632,plain,
% 3.54/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.54/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2046,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1662,c_632]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2154,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1659,c_628]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2723,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_2154,c_632]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4461,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK3,sK2))) != iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_2354,c_997,c_1002,c_2046,c_2723,c_3022]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4471,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_2155,c_4461]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6406,plain,
% 3.54/1.00      ( k2_xboole_0(X0,u1_struct_0(sK2)) = X1
% 3.54/1.00      | r2_hidden(sK0(X0,u1_struct_0(sK2),X1),X1) = iProver_top
% 3.54/1.00      | r2_hidden(sK0(X0,u1_struct_0(sK2),X1),X0) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_629,c_4471]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6649,plain,
% 3.54/1.00      ( k2_xboole_0(X0,u1_struct_0(sK2)) = X1
% 3.54/1.00      | r2_hidden(sK0(X0,u1_struct_0(sK2),X1),X0) = iProver_top
% 3.54/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_6406,c_632]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7206,plain,
% 3.54/1.00      ( k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = X0
% 3.54/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_6649,c_4471]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1761,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
% 3.54/1.00      | v2_struct_0(sK2) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_614,c_1752]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1296,plain,
% 3.54/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 3.54/1.00      | ~ l1_pre_topc(sK1)
% 3.54/1.00      | v2_struct_0(sK1)
% 3.54/1.00      | v2_struct_0(sK2)
% 3.54/1.00      | u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_916]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1889,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_1761,c_22,c_21,c_20,c_19,c_1296]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7221,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = X0
% 3.54/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_7206,c_1889]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7291,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_4173,c_7221]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6646,plain,
% 3.54/1.00      ( k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = X0
% 3.54/1.00      | r2_hidden(sK0(u1_struct_0(sK2),u1_struct_0(sK2),X0),X0) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_6406,c_4471]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6731,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = X0
% 3.54/1.00      | r2_hidden(sK0(u1_struct_0(sK2),u1_struct_0(sK2),X0),X0) = iProver_top ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_6646,c_1889]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1776,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK3,sK2))) = iProver_top
% 3.54/1.00      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1773,c_627]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4472,plain,
% 3.54/1.00      ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1776,c_4461]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7421,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK2)) = u1_struct_0(sK3) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_6731,c_4472]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8875,plain,
% 3.54/1.00      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = u1_struct_0(sK3) ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_7291,c_7421]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8884,plain,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_8875,c_617]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_31,plain,
% 3.54/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(contradiction,plain,
% 3.54/1.00      ( $false ),
% 3.54/1.00      inference(minisat,[status(thm)],[c_8884,c_31]) ).
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  ------                               Statistics
% 3.54/1.00  
% 3.54/1.00  ------ Selected
% 3.54/1.00  
% 3.54/1.00  total_time:                             0.302
% 3.54/1.00  
%------------------------------------------------------------------------------

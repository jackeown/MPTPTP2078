%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:47 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 419 expanded)
%              Number of clauses        :   71 (  95 expanded)
%              Number of leaves         :   16 ( 130 expanded)
%              Depth                    :   17
%              Number of atoms          :  672 (3955 expanded)
%              Number of equality atoms :  148 ( 755 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f29,plain,(
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
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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
        & v2_pre_topc(X0)
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
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f40,f39,f38,f37])).

fof(f67,plain,(
    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f55])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X5] :
      ( sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f68])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X4] :
      ( sK4 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f69])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_937,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_949,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2543,plain,
    ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_949])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_936,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_934,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_154,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_17,c_16,c_15])).

cnf(c_155,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_929,plain,
    ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_1417,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_929])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1985,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1417,c_28,c_30,c_31])).

cnf(c_1986,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1985])).

cnf(c_1994,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_1986])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1290,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_1498,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_2007,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1994,c_27,c_25,c_24,c_23,c_22,c_21,c_1498])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_951,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3551,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_951])).

cnf(c_4733,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_3551])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3952,plain,
    ( ~ m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
    | ~ r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_3953,plain,
    ( m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) != iProver_top
    | r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3952])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2233,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2234,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_2236,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2234])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1753,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1754,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1753])).

cnf(c_1756,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) != iProver_top
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1455,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_19,c_6])).

cnf(c_1456,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_1280,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(k1_tsep_1(sK1,X0,sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1381,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_1382,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_1358,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1359,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1343,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_18,c_6])).

cnf(c_1344,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1343])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1252,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    | r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
    | v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3))
    | ~ v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1253,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4)) = iProver_top
    | v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1233,plain,
    ( m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
    | ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    | v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3))
    | ~ v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1234,plain,
    ( m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_34,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_33,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4733,c_3953,c_2236,c_1756,c_1456,c_1382,c_1359,c_1344,c_1253,c_1234,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:04:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.03/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/0.99  
% 3.03/0.99  ------  iProver source info
% 3.03/0.99  
% 3.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/0.99  git: non_committed_changes: false
% 3.03/0.99  git: last_make_outside_of_git: false
% 3.03/0.99  
% 3.03/0.99  ------ 
% 3.03/0.99  ------ Parsing...
% 3.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/0.99  ------ Proving...
% 3.03/0.99  ------ Problem Properties 
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  clauses                                 28
% 3.03/0.99  conjectures                             10
% 3.03/0.99  EPR                                     11
% 3.03/0.99  Horn                                    18
% 3.03/0.99  unary                                   10
% 3.03/0.99  binary                                  3
% 3.03/0.99  lits                                    91
% 3.03/0.99  lits eq                                 6
% 3.03/0.99  fd_pure                                 0
% 3.03/0.99  fd_pseudo                               0
% 3.03/0.99  fd_cond                                 0
% 3.03/0.99  fd_pseudo_cond                          4
% 3.03/0.99  AC symbols                              0
% 3.03/0.99  
% 3.03/0.99  ------ Input Options Time Limit: Unbounded
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  ------ 
% 3.03/0.99  Current options:
% 3.03/0.99  ------ 
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  ------ Proving...
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS status Theorem for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  fof(f11,conjecture,(
% 3.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f12,negated_conjecture,(
% 3.03/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 3.03/0.99    inference(negated_conjecture,[],[f11])).
% 3.03/0.99  
% 3.03/0.99  fof(f13,plain,(
% 3.03/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 3.03/0.99    inference(rectify,[],[f12])).
% 3.03/0.99  
% 3.03/0.99  fof(f29,plain,(
% 3.03/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f13])).
% 3.03/0.99  
% 3.03/0.99  fof(f30,plain,(
% 3.03/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.03/0.99    inference(flattening,[],[f29])).
% 3.03/0.99  
% 3.03/0.99  fof(f40,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) => (! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))))) )),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f39,plain,(
% 3.03/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3)))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f38,plain,(
% 3.03/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f37,plain,(
% 3.03/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2)))) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f41,plain,(
% 3.03/0.99    (((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f40,f39,f38,f37])).
% 3.03/0.99  
% 3.03/0.99  fof(f67,plain,(
% 3.03/0.99    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f3,axiom,(
% 3.03/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f15,plain,(
% 3.03/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.03/0.99    inference(ennf_transformation,[],[f3])).
% 3.03/0.99  
% 3.03/0.99  fof(f16,plain,(
% 3.03/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.03/0.99    inference(flattening,[],[f15])).
% 3.03/0.99  
% 3.03/0.99  fof(f49,plain,(
% 3.03/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f16])).
% 3.03/0.99  
% 3.03/0.99  fof(f66,plain,(
% 3.03/0.99    m1_pre_topc(sK3,sK1)),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f64,plain,(
% 3.03/0.99    m1_pre_topc(sK2,sK1)),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f9,axiom,(
% 3.03/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f25,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f9])).
% 3.03/0.99  
% 3.03/0.99  fof(f26,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/0.99    inference(flattening,[],[f25])).
% 3.03/0.99  
% 3.03/0.99  fof(f36,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/0.99    inference(nnf_transformation,[],[f26])).
% 3.03/0.99  
% 3.03/0.99  fof(f55,plain,(
% 3.03/0.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f36])).
% 3.03/0.99  
% 3.03/0.99  fof(f73,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/0.99    inference(equality_resolution,[],[f55])).
% 3.03/0.99  
% 3.03/0.99  fof(f10,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f27,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f10])).
% 3.03/0.99  
% 3.03/0.99  fof(f28,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/0.99    inference(flattening,[],[f27])).
% 3.03/0.99  
% 3.03/0.99  fof(f57,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f28])).
% 3.03/0.99  
% 3.03/0.99  fof(f58,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f28])).
% 3.03/0.99  
% 3.03/0.99  fof(f59,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f28])).
% 3.03/0.99  
% 3.03/0.99  fof(f60,plain,(
% 3.03/0.99    ~v2_struct_0(sK1)),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f62,plain,(
% 3.03/0.99    l1_pre_topc(sK1)),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f63,plain,(
% 3.03/0.99    ~v2_struct_0(sK2)),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f65,plain,(
% 3.03/0.99    ~v2_struct_0(sK3)),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f1,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f31,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.03/0.99    inference(nnf_transformation,[],[f1])).
% 3.03/0.99  
% 3.03/0.99  fof(f32,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.03/0.99    inference(flattening,[],[f31])).
% 3.03/0.99  
% 3.03/0.99  fof(f33,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.03/0.99    inference(rectify,[],[f32])).
% 3.03/0.99  
% 3.03/0.99  fof(f34,plain,(
% 3.03/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f35,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f42,plain,(
% 3.03/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.03/0.99    inference(cnf_transformation,[],[f35])).
% 3.03/0.99  
% 3.03/0.99  fof(f72,plain,(
% 3.03/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.03/0.99    inference(equality_resolution,[],[f42])).
% 3.03/0.99  
% 3.03/0.99  fof(f4,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f17,plain,(
% 3.03/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.03/0.99    inference(ennf_transformation,[],[f4])).
% 3.03/0.99  
% 3.03/0.99  fof(f50,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f17])).
% 3.03/0.99  
% 3.03/0.99  fof(f5,axiom,(
% 3.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f18,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f5])).
% 3.03/0.99  
% 3.03/0.99  fof(f19,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.99    inference(flattening,[],[f18])).
% 3.03/0.99  
% 3.03/0.99  fof(f51,plain,(
% 3.03/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f19])).
% 3.03/0.99  
% 3.03/0.99  fof(f6,axiom,(
% 3.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f20,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.03/0.99    inference(ennf_transformation,[],[f6])).
% 3.03/0.99  
% 3.03/0.99  fof(f52,plain,(
% 3.03/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f20])).
% 3.03/0.99  
% 3.03/0.99  fof(f68,plain,(
% 3.03/0.99    ( ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f75,plain,(
% 3.03/0.99    ~m1_subset_1(sK4,u1_struct_0(sK2))),
% 3.03/0.99    inference(equality_resolution,[],[f68])).
% 3.03/0.99  
% 3.03/0.99  fof(f2,axiom,(
% 3.03/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f14,plain,(
% 3.03/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.03/0.99    inference(ennf_transformation,[],[f2])).
% 3.03/0.99  
% 3.03/0.99  fof(f48,plain,(
% 3.03/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f14])).
% 3.03/0.99  
% 3.03/0.99  fof(f69,plain,(
% 3.03/0.99    ( ! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f74,plain,(
% 3.03/0.99    ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.03/0.99    inference(equality_resolution,[],[f69])).
% 3.03/0.99  
% 3.03/0.99  fof(f8,axiom,(
% 3.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f23,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f8])).
% 3.03/0.99  
% 3.03/0.99  fof(f24,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/0.99    inference(flattening,[],[f23])).
% 3.03/0.99  
% 3.03/0.99  fof(f54,plain,(
% 3.03/0.99    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f24])).
% 3.03/0.99  
% 3.03/0.99  fof(f7,axiom,(
% 3.03/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f21,plain,(
% 3.03/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f7])).
% 3.03/0.99  
% 3.03/0.99  fof(f22,plain,(
% 3.03/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/0.99    inference(flattening,[],[f21])).
% 3.03/0.99  
% 3.03/0.99  fof(f53,plain,(
% 3.03/0.99    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f22])).
% 3.03/0.99  
% 3.03/0.99  fof(f61,plain,(
% 3.03/0.99    v2_pre_topc(sK1)),
% 3.03/0.99    inference(cnf_transformation,[],[f41])).
% 3.03/0.99  
% 3.03/0.99  cnf(c_20,negated_conjecture,
% 3.03/0.99      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 3.03/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_937,plain,
% 3.03/0.99      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_7,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_949,plain,
% 3.03/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.03/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.03/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2543,plain,
% 3.03/0.99      ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
% 3.03/0.99      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_937,c_949]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_21,negated_conjecture,
% 3.03/0.99      ( m1_pre_topc(sK3,sK1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_936,plain,
% 3.03/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_23,negated_conjecture,
% 3.03/0.99      ( m1_pre_topc(sK2,sK1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_934,plain,
% 3.03/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_14,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.03/0.99      | ~ m1_pre_topc(X2,X1)
% 3.03/0.99      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.03/0.99      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.03/0.99      | v2_struct_0(X1)
% 3.03/0.99      | v2_struct_0(X0)
% 3.03/0.99      | v2_struct_0(X2)
% 3.03/0.99      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.03/0.99      | ~ l1_pre_topc(X1)
% 3.03/0.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_17,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.03/0.99      | ~ m1_pre_topc(X2,X1)
% 3.03/0.99      | v2_struct_0(X1)
% 3.03/0.99      | v2_struct_0(X0)
% 3.03/0.99      | v2_struct_0(X2)
% 3.03/0.99      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.03/0.99      | ~ l1_pre_topc(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_16,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.03/0.99      | ~ m1_pre_topc(X2,X1)
% 3.03/0.99      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.03/0.99      | v2_struct_0(X1)
% 3.03/0.99      | v2_struct_0(X0)
% 3.03/0.99      | v2_struct_0(X2)
% 3.03/0.99      | ~ l1_pre_topc(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_15,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.03/0.99      | ~ m1_pre_topc(X2,X1)
% 3.03/0.99      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.03/0.99      | v2_struct_0(X1)
% 3.03/0.99      | v2_struct_0(X0)
% 3.03/0.99      | v2_struct_0(X2)
% 3.03/0.99      | ~ l1_pre_topc(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_154,plain,
% 3.03/0.99      ( v2_struct_0(X2)
% 3.03/0.99      | v2_struct_0(X0)
% 3.03/0.99      | v2_struct_0(X1)
% 3.03/0.99      | ~ m1_pre_topc(X2,X1)
% 3.03/0.99      | ~ m1_pre_topc(X0,X1)
% 3.03/0.99      | ~ l1_pre_topc(X1)
% 3.03/0.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_14,c_17,c_16,c_15]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_155,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.03/0.99      | ~ m1_pre_topc(X2,X1)
% 3.03/0.99      | v2_struct_0(X0)
% 3.03/0.99      | v2_struct_0(X1)
% 3.03/0.99      | v2_struct_0(X2)
% 3.03/0.99      | ~ l1_pre_topc(X1)
% 3.03/0.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.03/0.99      inference(renaming,[status(thm)],[c_154]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_929,plain,
% 3.03/0.99      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
% 3.03/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.03/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.03/0.99      | v2_struct_0(X0) = iProver_top
% 3.03/0.99      | v2_struct_0(X1) = iProver_top
% 3.03/0.99      | v2_struct_0(X2) = iProver_top
% 3.03/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1417,plain,
% 3.03/0.99      ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
% 3.03/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.03/0.99      | v2_struct_0(X0) = iProver_top
% 3.03/0.99      | v2_struct_0(sK1) = iProver_top
% 3.03/0.99      | v2_struct_0(sK2) = iProver_top
% 3.03/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_934,c_929]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_27,negated_conjecture,
% 3.03/0.99      ( ~ v2_struct_0(sK1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_28,plain,
% 3.03/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_25,negated_conjecture,
% 3.03/0.99      ( l1_pre_topc(sK1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_30,plain,
% 3.03/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_24,negated_conjecture,
% 3.03/0.99      ( ~ v2_struct_0(sK2) ),
% 3.03/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_31,plain,
% 3.03/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1985,plain,
% 3.03/0.99      ( v2_struct_0(X0) = iProver_top
% 3.03/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.03/0.99      | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_1417,c_28,c_30,c_31]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1986,plain,
% 3.03/0.99      ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
% 3.03/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.03/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.03/0.99      inference(renaming,[status(thm)],[c_1985]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1994,plain,
% 3.03/0.99      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.03/0.99      | v2_struct_0(sK3) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_936,c_1986]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_22,negated_conjecture,
% 3.03/0.99      ( ~ v2_struct_0(sK3) ),
% 3.03/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1290,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,sK1)
% 3.03/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.03/0.99      | v2_struct_0(X0)
% 3.03/0.99      | v2_struct_0(sK1)
% 3.03/0.99      | v2_struct_0(sK3)
% 3.03/0.99      | ~ l1_pre_topc(sK1)
% 3.03/0.99      | u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_155]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1498,plain,
% 3.03/0.99      ( ~ m1_pre_topc(sK2,sK1)
% 3.03/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.03/0.99      | v2_struct_0(sK1)
% 3.03/0.99      | v2_struct_0(sK2)
% 3.03/0.99      | v2_struct_0(sK3)
% 3.03/0.99      | ~ l1_pre_topc(sK1)
% 3.03/0.99      | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1290]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2007,plain,
% 3.03/0.99      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_1994,c_27,c_25,c_24,c_23,c_22,c_21,c_1498]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_5,plain,
% 3.03/0.99      ( r2_hidden(X0,X1)
% 3.03/0.99      | r2_hidden(X0,X2)
% 3.03/0.99      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_951,plain,
% 3.03/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.03/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.03/0.99      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3551,plain,
% 3.03/0.99      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 3.03/0.99      | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
% 3.03/0.99      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_2007,c_951]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4733,plain,
% 3.03/0.99      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 3.03/0.99      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 3.03/0.99      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_2543,c_3551]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_8,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.03/0.99      | ~ r2_hidden(X2,X0)
% 3.03/0.99      | ~ v1_xboole_0(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1345,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
% 3.03/0.99      | ~ r2_hidden(X1,X0)
% 3.03/0.99      | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3952,plain,
% 3.03/0.99      ( ~ m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
% 3.03/0.99      | ~ r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
% 3.03/0.99      | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1345]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3953,plain,
% 3.03/0.99      ( m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) != iProver_top
% 3.03/0.99      | r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4)) != iProver_top
% 3.03/0.99      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_3952]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_9,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.03/0.99      | ~ l1_pre_topc(X1)
% 3.03/0.99      | ~ v2_pre_topc(X1)
% 3.03/0.99      | v2_pre_topc(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2233,plain,
% 3.03/0.99      ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0)
% 3.03/0.99      | ~ l1_pre_topc(X0)
% 3.03/0.99      | ~ v2_pre_topc(X0)
% 3.03/0.99      | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2234,plain,
% 3.03/0.99      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0) != iProver_top
% 3.03/0.99      | l1_pre_topc(X0) != iProver_top
% 3.03/0.99      | v2_pre_topc(X0) != iProver_top
% 3.03/0.99      | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2236,plain,
% 3.03/0.99      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) != iProver_top
% 3.03/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.03/0.99      | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
% 3.03/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_2234]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_10,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1753,plain,
% 3.03/0.99      ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0)
% 3.03/0.99      | ~ l1_pre_topc(X0)
% 3.03/0.99      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1754,plain,
% 3.03/0.99      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0) != iProver_top
% 3.03/0.99      | l1_pre_topc(X0) != iProver_top
% 3.03/0.99      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1753]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1756,plain,
% 3.03/0.99      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) != iProver_top
% 3.03/0.99      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
% 3.03/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1754]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_19,negated_conjecture,
% 3.03/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_6,plain,
% 3.03/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1455,plain,
% 3.03/0.99      ( ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 3.03/0.99      inference(resolution,[status(thm)],[c_19,c_6]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1456,plain,
% 3.03/0.99      ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1280,plain,
% 3.03/0.99      ( ~ m1_pre_topc(X0,sK1)
% 3.03/0.99      | m1_pre_topc(k1_tsep_1(sK1,X0,sK3),sK1)
% 3.03/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.03/0.99      | v2_struct_0(X0)
% 3.03/0.99      | v2_struct_0(sK1)
% 3.03/0.99      | v2_struct_0(sK3)
% 3.03/0.99      | ~ l1_pre_topc(sK1) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1381,plain,
% 3.03/0.99      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1)
% 3.03/0.99      | ~ m1_pre_topc(sK2,sK1)
% 3.03/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.03/0.99      | v2_struct_0(sK1)
% 3.03/0.99      | v2_struct_0(sK2)
% 3.03/0.99      | v2_struct_0(sK3)
% 3.03/0.99      | ~ l1_pre_topc(sK1) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1280]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1382,plain,
% 3.03/0.99      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) = iProver_top
% 3.03/0.99      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.03/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 3.03/0.99      | v2_struct_0(sK1) = iProver_top
% 3.03/0.99      | v2_struct_0(sK2) = iProver_top
% 3.03/0.99      | v2_struct_0(sK3) = iProver_top
% 3.03/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1358,plain,
% 3.03/0.99      ( ~ m1_pre_topc(sK2,sK1)
% 3.03/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.03/0.99      | ~ v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 3.03/0.99      | v2_struct_0(sK1)
% 3.03/0.99      | v2_struct_0(sK2)
% 3.03/0.99      | v2_struct_0(sK3)
% 3.03/0.99      | ~ l1_pre_topc(sK1) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1359,plain,
% 3.03/0.99      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.03/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 3.03/0.99      | v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
% 3.03/0.99      | v2_struct_0(sK1) = iProver_top
% 3.03/0.99      | v2_struct_0(sK2) = iProver_top
% 3.03/0.99      | v2_struct_0(sK3) = iProver_top
% 3.03/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1358]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_18,negated_conjecture,
% 3.03/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1343,plain,
% 3.03/0.99      ( ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
% 3.03/0.99      inference(resolution,[status(thm)],[c_18,c_6]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1344,plain,
% 3.03/0.99      ( r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1343]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_12,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.03/0.99      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 3.03/0.99      | v2_struct_0(X1)
% 3.03/0.99      | ~ l1_pre_topc(X1)
% 3.03/0.99      | ~ v2_pre_topc(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1252,plain,
% 3.03/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
% 3.03/0.99      | r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
% 3.03/0.99      | v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 3.03/0.99      | ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3))
% 3.03/0.99      | ~ v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1253,plain,
% 3.03/0.99      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 3.03/0.99      | r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4)) = iProver_top
% 3.03/0.99      | v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
% 3.03/0.99      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
% 3.03/0.99      | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_11,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.03/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.99      | v2_struct_0(X1)
% 3.03/0.99      | ~ l1_pre_topc(X1)
% 3.03/0.99      | ~ v2_pre_topc(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1233,plain,
% 3.03/0.99      ( m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
% 3.03/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
% 3.03/0.99      | v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 3.03/0.99      | ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3))
% 3.03/0.99      | ~ v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1234,plain,
% 3.03/0.99      ( m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) = iProver_top
% 3.03/0.99      | m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 3.03/0.99      | v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
% 3.03/0.99      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
% 3.03/0.99      | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_35,plain,
% 3.03/0.99      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_34,plain,
% 3.03/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_33,plain,
% 3.03/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_32,plain,
% 3.03/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_26,negated_conjecture,
% 3.03/0.99      ( v2_pre_topc(sK1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_29,plain,
% 3.03/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(contradiction,plain,
% 3.03/0.99      ( $false ),
% 3.03/0.99      inference(minisat,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_4733,c_3953,c_2236,c_1756,c_1456,c_1382,c_1359,c_1344,
% 3.03/0.99                 c_1253,c_1234,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28]) ).
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  ------                               Statistics
% 3.03/0.99  
% 3.03/0.99  ------ Selected
% 3.03/0.99  
% 3.03/0.99  total_time:                             0.137
% 3.03/0.99  
%------------------------------------------------------------------------------

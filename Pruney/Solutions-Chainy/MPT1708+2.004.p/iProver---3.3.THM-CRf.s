%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:49 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  153 (1675 expanded)
%              Number of clauses        :   89 ( 353 expanded)
%              Number of leaves         :   14 ( 507 expanded)
%              Depth                    :   30
%              Number of atoms          :  772 (17182 expanded)
%              Number of equality atoms :  232 (3258 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
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
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f22,plain,(
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
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
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
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
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
              ( sK4 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) )
          | ! [X5] :
              ( sK4 != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
        & m1_subset_1(sK4,u1_struct_0(k2_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                  | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,sK3))) )
        & ~ r1_tsep_1(X1,sK3)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,sK2,X2))) )
            & ~ r1_tsep_1(sK2,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ! [X4] :
          ( sK4 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
      | ! [X5] :
          ( sK4 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) )
    & m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
    & ~ r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f34,f33,f32,f31])).

fof(f62,plain,(
    m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(X3)
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
    inference(definition_unfolding,[],[f50,f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(k2_tsep_1(X0,X1,X2))
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
    inference(equality_resolution,[],[f65])).

fof(f61,plain,(
    ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X4,X5] :
      ( sK4 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f71,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f70])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1248,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1236,plain,
    ( m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1242,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1867,plain,
    ( r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1242])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_30,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_31,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1477,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
    | r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1478,plain,
    ( m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1477])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_287,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_10,c_12])).

cnf(c_1548,plain,
    ( v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ l1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_1549,plain,
    ( v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) = iProver_top
    | l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1548])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1514,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK1,sK2,X0))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1588,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_1589,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1772,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1773,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_1775,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1) != iProver_top
    | l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1524,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(k2_tsep_1(sK1,sK2,X0),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1788,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_1789,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_1957,plain,
    ( r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1867,c_27,c_28,c_29,c_30,c_31,c_32,c_34,c_1478,c_1549,c_1589,c_1775,c_1789])).

cnf(c_1233,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1239,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | v1_pre_topc(k2_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1240,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
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
    | k4_xboole_0(u1_struct_0(X0),k4_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) = u1_struct_0(k2_tsep_1(X2,X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_305,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | ~ v1_pre_topc(k2_tsep_1(X1,X0,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | k4_xboole_0(u1_struct_0(X0),k4_xboole_0(u1_struct_0(X0),u1_struct_0(X2))) = u1_struct_0(k2_tsep_1(X1,X0,X2))
    | sK2 != X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_306,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK2,sK3),X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK2,sK3))
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK2,sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_310,plain,
    ( ~ m1_pre_topc(k2_tsep_1(X0,sK2,sK3),X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ v1_pre_topc(k2_tsep_1(X0,sK2,sK3))
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(X0,sK2,sK3))
    | ~ l1_pre_topc(X0)
    | k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_24,c_22])).

cnf(c_1228,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
    | m1_pre_topc(k2_tsep_1(X0,sK2,sK3),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK2,sK3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_5487,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK2,sK3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1228])).

cnf(c_5797,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v1_pre_topc(k2_tsep_1(X0,sK2,sK3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5487,c_29,c_31])).

cnf(c_5810,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_5797])).

cnf(c_6072,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5810,c_29,c_31])).

cnf(c_1238,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(k2_tsep_1(X1,X0,X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6084,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6072,c_1238])).

cnf(c_6089,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6084,c_29,c_31])).

cnf(c_6100,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_6089])).

cnf(c_313,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
    | v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_1504,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v1_pre_topc(k2_tsep_1(sK1,sK2,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1576,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_6117,plain,
    ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6100,c_26,c_25,c_24,c_23,c_22,c_21,c_313,c_1576,c_1588,c_1788])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1247,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6205,plain,
    ( r2_hidden(X0,k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6117,c_1247])).

cnf(c_6312,plain,
    ( r2_hidden(sK4,k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_6205])).

cnf(c_6352,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_6312])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1246,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6204,plain,
    ( r2_hidden(X0,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6117,c_1246])).

cnf(c_6258,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_6204])).

cnf(c_6407,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6352,c_6258])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6412,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6407,c_1243])).

cnf(c_6305,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6258,c_1243])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1237,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6387,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6305,c_1237])).

cnf(c_6419,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6412,c_6387])).

cnf(c_1229,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_6540,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6419,c_1229])).

cnf(c_1241,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1808,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_1241])).

cnf(c_7198,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6540,c_28,c_29,c_1808])).

cnf(c_7203,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7198,c_1229])).

cnf(c_1235,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1807,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_1241])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7203,c_1807,c_31,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.14/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.99  
% 3.14/0.99  ------  iProver source info
% 3.14/0.99  
% 3.14/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.99  git: non_committed_changes: false
% 3.14/0.99  git: last_make_outside_of_git: false
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/0.99  --prep_def_merge_mbd                    true
% 3.14/0.99  --prep_def_merge_tr_red                 false
% 3.14/0.99  --prep_def_merge_tr_cl                  false
% 3.14/0.99  --smt_preprocessing                     true
% 3.14/0.99  --smt_ac_axioms                         fast
% 3.14/0.99  --preprocessed_out                      false
% 3.14/0.99  --preprocessed_stats                    false
% 3.14/0.99  
% 3.14/0.99  ------ Abstraction refinement Options
% 3.14/0.99  
% 3.14/0.99  --abstr_ref                             []
% 3.14/0.99  --abstr_ref_prep                        false
% 3.14/0.99  --abstr_ref_until_sat                   false
% 3.14/0.99  --abstr_ref_sig_restrict                funpre
% 3.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.99  --abstr_ref_under                       []
% 3.14/0.99  
% 3.14/0.99  ------ SAT Options
% 3.14/0.99  
% 3.14/0.99  --sat_mode                              false
% 3.14/0.99  --sat_fm_restart_options                ""
% 3.14/0.99  --sat_gr_def                            false
% 3.14/0.99  --sat_epr_types                         true
% 3.14/0.99  --sat_non_cyclic_types                  false
% 3.14/0.99  --sat_finite_models                     false
% 3.14/0.99  --sat_fm_lemmas                         false
% 3.14/0.99  --sat_fm_prep                           false
% 3.14/0.99  --sat_fm_uc_incr                        true
% 3.14/0.99  --sat_out_model                         small
% 3.14/0.99  --sat_out_clauses                       false
% 3.14/0.99  
% 3.14/0.99  ------ QBF Options
% 3.14/0.99  
% 3.14/0.99  --qbf_mode                              false
% 3.14/0.99  --qbf_elim_univ                         false
% 3.14/0.99  --qbf_dom_inst                          none
% 3.14/0.99  --qbf_dom_pre_inst                      false
% 3.14/0.99  --qbf_sk_in                             false
% 3.14/0.99  --qbf_pred_elim                         true
% 3.14/0.99  --qbf_split                             512
% 3.14/0.99  
% 3.14/0.99  ------ BMC1 Options
% 3.14/0.99  
% 3.14/0.99  --bmc1_incremental                      false
% 3.14/0.99  --bmc1_axioms                           reachable_all
% 3.14/0.99  --bmc1_min_bound                        0
% 3.14/0.99  --bmc1_max_bound                        -1
% 3.14/0.99  --bmc1_max_bound_default                -1
% 3.14/0.99  --bmc1_symbol_reachability              true
% 3.14/0.99  --bmc1_property_lemmas                  false
% 3.14/0.99  --bmc1_k_induction                      false
% 3.14/0.99  --bmc1_non_equiv_states                 false
% 3.14/0.99  --bmc1_deadlock                         false
% 3.14/0.99  --bmc1_ucm                              false
% 3.14/0.99  --bmc1_add_unsat_core                   none
% 3.14/0.99  --bmc1_unsat_core_children              false
% 3.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.99  --bmc1_out_stat                         full
% 3.14/0.99  --bmc1_ground_init                      false
% 3.14/0.99  --bmc1_pre_inst_next_state              false
% 3.14/0.99  --bmc1_pre_inst_state                   false
% 3.14/0.99  --bmc1_pre_inst_reach_state             false
% 3.14/0.99  --bmc1_out_unsat_core                   false
% 3.14/0.99  --bmc1_aig_witness_out                  false
% 3.14/0.99  --bmc1_verbose                          false
% 3.14/0.99  --bmc1_dump_clauses_tptp                false
% 3.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.99  --bmc1_dump_file                        -
% 3.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.99  --bmc1_ucm_extend_mode                  1
% 3.14/0.99  --bmc1_ucm_init_mode                    2
% 3.14/0.99  --bmc1_ucm_cone_mode                    none
% 3.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.99  --bmc1_ucm_relax_model                  4
% 3.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.99  --bmc1_ucm_layered_model                none
% 3.14/0.99  --bmc1_ucm_max_lemma_size               10
% 3.14/0.99  
% 3.14/0.99  ------ AIG Options
% 3.14/0.99  
% 3.14/0.99  --aig_mode                              false
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation Options
% 3.14/0.99  
% 3.14/0.99  --instantiation_flag                    true
% 3.14/0.99  --inst_sos_flag                         false
% 3.14/0.99  --inst_sos_phase                        true
% 3.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel_side                     num_symb
% 3.14/0.99  --inst_solver_per_active                1400
% 3.14/0.99  --inst_solver_calls_frac                1.
% 3.14/0.99  --inst_passive_queue_type               priority_queues
% 3.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.99  --inst_passive_queues_freq              [25;2]
% 3.14/0.99  --inst_dismatching                      true
% 3.14/0.99  --inst_eager_unprocessed_to_passive     true
% 3.14/0.99  --inst_prop_sim_given                   true
% 3.14/0.99  --inst_prop_sim_new                     false
% 3.14/0.99  --inst_subs_new                         false
% 3.14/0.99  --inst_eq_res_simp                      false
% 3.14/0.99  --inst_subs_given                       false
% 3.14/0.99  --inst_orphan_elimination               true
% 3.14/0.99  --inst_learning_loop_flag               true
% 3.14/0.99  --inst_learning_start                   3000
% 3.14/0.99  --inst_learning_factor                  2
% 3.14/0.99  --inst_start_prop_sim_after_learn       3
% 3.14/0.99  --inst_sel_renew                        solver
% 3.14/0.99  --inst_lit_activity_flag                true
% 3.14/0.99  --inst_restr_to_given                   false
% 3.14/0.99  --inst_activity_threshold               500
% 3.14/0.99  --inst_out_proof                        true
% 3.14/0.99  
% 3.14/0.99  ------ Resolution Options
% 3.14/0.99  
% 3.14/0.99  --resolution_flag                       true
% 3.14/0.99  --res_lit_sel                           adaptive
% 3.14/0.99  --res_lit_sel_side                      none
% 3.14/0.99  --res_ordering                          kbo
% 3.14/0.99  --res_to_prop_solver                    active
% 3.14/0.99  --res_prop_simpl_new                    false
% 3.14/0.99  --res_prop_simpl_given                  true
% 3.14/0.99  --res_passive_queue_type                priority_queues
% 3.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.99  --res_passive_queues_freq               [15;5]
% 3.14/0.99  --res_forward_subs                      full
% 3.14/0.99  --res_backward_subs                     full
% 3.14/0.99  --res_forward_subs_resolution           true
% 3.14/0.99  --res_backward_subs_resolution          true
% 3.14/0.99  --res_orphan_elimination                true
% 3.14/0.99  --res_time_limit                        2.
% 3.14/0.99  --res_out_proof                         true
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Options
% 3.14/0.99  
% 3.14/0.99  --superposition_flag                    true
% 3.14/0.99  --sup_passive_queue_type                priority_queues
% 3.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.99  --demod_completeness_check              fast
% 3.14/0.99  --demod_use_ground                      true
% 3.14/0.99  --sup_to_prop_solver                    passive
% 3.14/0.99  --sup_prop_simpl_new                    true
% 3.14/0.99  --sup_prop_simpl_given                  true
% 3.14/0.99  --sup_fun_splitting                     false
% 3.14/0.99  --sup_smt_interval                      50000
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Simplification Setup
% 3.14/0.99  
% 3.14/0.99  --sup_indices_passive                   []
% 3.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_full_bw                           [BwDemod]
% 3.14/0.99  --sup_immed_triv                        [TrivRules]
% 3.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_immed_bw_main                     []
% 3.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  
% 3.14/0.99  ------ Combination Options
% 3.14/0.99  
% 3.14/0.99  --comb_res_mult                         3
% 3.14/0.99  --comb_sup_mult                         2
% 3.14/0.99  --comb_inst_mult                        10
% 3.14/0.99  
% 3.14/0.99  ------ Debug Options
% 3.14/0.99  
% 3.14/0.99  --dbg_backtrace                         false
% 3.14/0.99  --dbg_dump_prop_clauses                 false
% 3.14/0.99  --dbg_dump_prop_clauses_file            -
% 3.14/0.99  --dbg_out_stat                          false
% 3.14/0.99  ------ Parsing...
% 3.14/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.99  ------ Proving...
% 3.14/0.99  ------ Problem Properties 
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  clauses                                 25
% 3.14/0.99  conjectures                             8
% 3.14/0.99  EPR                                     11
% 3.14/0.99  Horn                                    14
% 3.14/0.99  unary                                   7
% 3.14/0.99  binary                                  3
% 3.14/0.99  lits                                    82
% 3.14/0.99  lits eq                                 6
% 3.14/0.99  fd_pure                                 0
% 3.14/0.99  fd_pseudo                               0
% 3.14/0.99  fd_cond                                 0
% 3.14/0.99  fd_pseudo_cond                          4
% 3.14/0.99  AC symbols                              0
% 3.14/0.99  
% 3.14/0.99  ------ Schedule dynamic 5 is on 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  Current options:
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/0.99  --prep_def_merge_mbd                    true
% 3.14/0.99  --prep_def_merge_tr_red                 false
% 3.14/0.99  --prep_def_merge_tr_cl                  false
% 3.14/0.99  --smt_preprocessing                     true
% 3.14/0.99  --smt_ac_axioms                         fast
% 3.14/0.99  --preprocessed_out                      false
% 3.14/0.99  --preprocessed_stats                    false
% 3.14/0.99  
% 3.14/0.99  ------ Abstraction refinement Options
% 3.14/0.99  
% 3.14/0.99  --abstr_ref                             []
% 3.14/0.99  --abstr_ref_prep                        false
% 3.14/0.99  --abstr_ref_until_sat                   false
% 3.14/0.99  --abstr_ref_sig_restrict                funpre
% 3.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.99  --abstr_ref_under                       []
% 3.14/0.99  
% 3.14/0.99  ------ SAT Options
% 3.14/0.99  
% 3.14/0.99  --sat_mode                              false
% 3.14/0.99  --sat_fm_restart_options                ""
% 3.14/0.99  --sat_gr_def                            false
% 3.14/0.99  --sat_epr_types                         true
% 3.14/0.99  --sat_non_cyclic_types                  false
% 3.14/0.99  --sat_finite_models                     false
% 3.14/0.99  --sat_fm_lemmas                         false
% 3.14/0.99  --sat_fm_prep                           false
% 3.14/0.99  --sat_fm_uc_incr                        true
% 3.14/0.99  --sat_out_model                         small
% 3.14/0.99  --sat_out_clauses                       false
% 3.14/0.99  
% 3.14/0.99  ------ QBF Options
% 3.14/0.99  
% 3.14/0.99  --qbf_mode                              false
% 3.14/0.99  --qbf_elim_univ                         false
% 3.14/0.99  --qbf_dom_inst                          none
% 3.14/0.99  --qbf_dom_pre_inst                      false
% 3.14/0.99  --qbf_sk_in                             false
% 3.14/0.99  --qbf_pred_elim                         true
% 3.14/0.99  --qbf_split                             512
% 3.14/0.99  
% 3.14/0.99  ------ BMC1 Options
% 3.14/0.99  
% 3.14/0.99  --bmc1_incremental                      false
% 3.14/0.99  --bmc1_axioms                           reachable_all
% 3.14/0.99  --bmc1_min_bound                        0
% 3.14/0.99  --bmc1_max_bound                        -1
% 3.14/0.99  --bmc1_max_bound_default                -1
% 3.14/0.99  --bmc1_symbol_reachability              true
% 3.14/0.99  --bmc1_property_lemmas                  false
% 3.14/0.99  --bmc1_k_induction                      false
% 3.14/0.99  --bmc1_non_equiv_states                 false
% 3.14/0.99  --bmc1_deadlock                         false
% 3.14/0.99  --bmc1_ucm                              false
% 3.14/0.99  --bmc1_add_unsat_core                   none
% 3.14/0.99  --bmc1_unsat_core_children              false
% 3.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.99  --bmc1_out_stat                         full
% 3.14/0.99  --bmc1_ground_init                      false
% 3.14/0.99  --bmc1_pre_inst_next_state              false
% 3.14/0.99  --bmc1_pre_inst_state                   false
% 3.14/0.99  --bmc1_pre_inst_reach_state             false
% 3.14/0.99  --bmc1_out_unsat_core                   false
% 3.14/0.99  --bmc1_aig_witness_out                  false
% 3.14/0.99  --bmc1_verbose                          false
% 3.14/0.99  --bmc1_dump_clauses_tptp                false
% 3.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.99  --bmc1_dump_file                        -
% 3.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.99  --bmc1_ucm_extend_mode                  1
% 3.14/0.99  --bmc1_ucm_init_mode                    2
% 3.14/0.99  --bmc1_ucm_cone_mode                    none
% 3.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.99  --bmc1_ucm_relax_model                  4
% 3.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.99  --bmc1_ucm_layered_model                none
% 3.14/0.99  --bmc1_ucm_max_lemma_size               10
% 3.14/0.99  
% 3.14/0.99  ------ AIG Options
% 3.14/0.99  
% 3.14/0.99  --aig_mode                              false
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation Options
% 3.14/0.99  
% 3.14/0.99  --instantiation_flag                    true
% 3.14/0.99  --inst_sos_flag                         false
% 3.14/0.99  --inst_sos_phase                        true
% 3.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel_side                     none
% 3.14/0.99  --inst_solver_per_active                1400
% 3.14/0.99  --inst_solver_calls_frac                1.
% 3.14/0.99  --inst_passive_queue_type               priority_queues
% 3.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.99  --inst_passive_queues_freq              [25;2]
% 3.14/0.99  --inst_dismatching                      true
% 3.14/0.99  --inst_eager_unprocessed_to_passive     true
% 3.14/0.99  --inst_prop_sim_given                   true
% 3.14/0.99  --inst_prop_sim_new                     false
% 3.14/0.99  --inst_subs_new                         false
% 3.14/0.99  --inst_eq_res_simp                      false
% 3.14/0.99  --inst_subs_given                       false
% 3.14/0.99  --inst_orphan_elimination               true
% 3.14/0.99  --inst_learning_loop_flag               true
% 3.14/0.99  --inst_learning_start                   3000
% 3.14/0.99  --inst_learning_factor                  2
% 3.14/0.99  --inst_start_prop_sim_after_learn       3
% 3.14/0.99  --inst_sel_renew                        solver
% 3.14/0.99  --inst_lit_activity_flag                true
% 3.14/0.99  --inst_restr_to_given                   false
% 3.14/0.99  --inst_activity_threshold               500
% 3.14/0.99  --inst_out_proof                        true
% 3.14/0.99  
% 3.14/0.99  ------ Resolution Options
% 3.14/0.99  
% 3.14/0.99  --resolution_flag                       false
% 3.14/0.99  --res_lit_sel                           adaptive
% 3.14/0.99  --res_lit_sel_side                      none
% 3.14/0.99  --res_ordering                          kbo
% 3.14/0.99  --res_to_prop_solver                    active
% 3.14/0.99  --res_prop_simpl_new                    false
% 3.14/0.99  --res_prop_simpl_given                  true
% 3.14/0.99  --res_passive_queue_type                priority_queues
% 3.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.99  --res_passive_queues_freq               [15;5]
% 3.14/0.99  --res_forward_subs                      full
% 3.14/0.99  --res_backward_subs                     full
% 3.14/0.99  --res_forward_subs_resolution           true
% 3.14/0.99  --res_backward_subs_resolution          true
% 3.14/0.99  --res_orphan_elimination                true
% 3.14/0.99  --res_time_limit                        2.
% 3.14/0.99  --res_out_proof                         true
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Options
% 3.14/0.99  
% 3.14/0.99  --superposition_flag                    true
% 3.14/0.99  --sup_passive_queue_type                priority_queues
% 3.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.99  --demod_completeness_check              fast
% 3.14/0.99  --demod_use_ground                      true
% 3.14/0.99  --sup_to_prop_solver                    passive
% 3.14/0.99  --sup_prop_simpl_new                    true
% 3.14/0.99  --sup_prop_simpl_given                  true
% 3.14/0.99  --sup_fun_splitting                     false
% 3.14/0.99  --sup_smt_interval                      50000
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Simplification Setup
% 3.14/0.99  
% 3.14/0.99  --sup_indices_passive                   []
% 3.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_full_bw                           [BwDemod]
% 3.14/0.99  --sup_immed_triv                        [TrivRules]
% 3.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_immed_bw_main                     []
% 3.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  
% 3.14/0.99  ------ Combination Options
% 3.14/0.99  
% 3.14/0.99  --comb_res_mult                         3
% 3.14/0.99  --comb_sup_mult                         2
% 3.14/0.99  --comb_inst_mult                        10
% 3.14/0.99  
% 3.14/0.99  ------ Debug Options
% 3.14/0.99  
% 3.14/0.99  --dbg_backtrace                         false
% 3.14/0.99  --dbg_dump_prop_clauses                 false
% 3.14/0.99  --dbg_dump_prop_clauses_file            -
% 3.14/0.99  --dbg_out_stat                          false
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  ------ Proving...
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  % SZS status Theorem for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  fof(f1,axiom,(
% 3.14/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f24,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.14/0.99    inference(nnf_transformation,[],[f1])).
% 3.14/0.99  
% 3.14/0.99  fof(f25,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.14/0.99    inference(flattening,[],[f24])).
% 3.14/0.99  
% 3.14/0.99  fof(f26,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.14/0.99    inference(rectify,[],[f25])).
% 3.14/0.99  
% 3.14/0.99  fof(f27,plain,(
% 3.14/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f28,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f38,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.14/0.99    inference(cnf_transformation,[],[f28])).
% 3.14/0.99  
% 3.14/0.99  fof(f66,plain,(
% 3.14/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.14/0.99    inference(equality_resolution,[],[f38])).
% 3.14/0.99  
% 3.14/0.99  fof(f9,conjecture,(
% 3.14/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f10,negated_conjecture,(
% 3.14/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 3.14/0.99    inference(negated_conjecture,[],[f9])).
% 3.14/0.99  
% 3.14/0.99  fof(f11,plain,(
% 3.14/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 3.14/0.99    inference(rectify,[],[f10])).
% 3.14/0.99  
% 3.14/0.99  fof(f12,plain,(
% 3.14/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 3.14/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.14/0.99  
% 3.14/0.99  fof(f22,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f12])).
% 3.14/0.99  
% 3.14/0.99  fof(f23,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f22])).
% 3.14/0.99  
% 3.14/0.99  fof(f34,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) => ((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(sK4,u1_struct_0(k2_tsep_1(X0,X1,X2))))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f33,plain,(
% 3.14/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,sK3)))) & ~r1_tsep_1(X1,sK3) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f32,plain,(
% 3.14/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,sK2,X2)))) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f31,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f35,plain,(
% 3.14/0.99    ((((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) | ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2)))) & m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f34,f33,f32,f31])).
% 3.14/0.99  
% 3.14/0.99  fof(f62,plain,(
% 3.14/0.99    m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f3,axiom,(
% 3.14/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f13,plain,(
% 3.14/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f3])).
% 3.14/0.99  
% 3.14/0.99  fof(f29,plain,(
% 3.14/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.14/0.99    inference(nnf_transformation,[],[f13])).
% 3.14/0.99  
% 3.14/0.99  fof(f43,plain,(
% 3.14/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f29])).
% 3.14/0.99  
% 3.14/0.99  fof(f55,plain,(
% 3.14/0.99    ~v2_struct_0(sK1)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f56,plain,(
% 3.14/0.99    l1_pre_topc(sK1)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f57,plain,(
% 3.14/0.99    ~v2_struct_0(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f58,plain,(
% 3.14/0.99    m1_pre_topc(sK2,sK1)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f59,plain,(
% 3.14/0.99    ~v2_struct_0(sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f60,plain,(
% 3.14/0.99    m1_pre_topc(sK3,sK1)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f4,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f14,plain,(
% 3.14/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f4])).
% 3.14/0.99  
% 3.14/0.99  fof(f47,plain,(
% 3.14/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f14])).
% 3.14/0.99  
% 3.14/0.99  fof(f6,axiom,(
% 3.14/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f16,plain,(
% 3.14/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f6])).
% 3.14/0.99  
% 3.14/0.99  fof(f17,plain,(
% 3.14/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f16])).
% 3.14/0.99  
% 3.14/0.99  fof(f49,plain,(
% 3.14/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f17])).
% 3.14/0.99  
% 3.14/0.99  fof(f8,axiom,(
% 3.14/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f20,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f8])).
% 3.14/0.99  
% 3.14/0.99  fof(f21,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f20])).
% 3.14/0.99  
% 3.14/0.99  fof(f52,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f5,axiom,(
% 3.14/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f15,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f5])).
% 3.14/0.99  
% 3.14/0.99  fof(f48,plain,(
% 3.14/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f15])).
% 3.14/0.99  
% 3.14/0.99  fof(f54,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f53,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f7,axiom,(
% 3.14/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)))))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f18,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f7])).
% 3.14/0.99  
% 3.14/0.99  fof(f19,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f18])).
% 3.14/0.99  
% 3.14/0.99  fof(f30,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(nnf_transformation,[],[f19])).
% 3.14/0.99  
% 3.14/0.99  fof(f50,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f2,axiom,(
% 3.14/0.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f42,plain,(
% 3.14/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f2])).
% 3.14/0.99  
% 3.14/0.99  fof(f65,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(X3) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(definition_unfolding,[],[f50,f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f69,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(equality_resolution,[],[f65])).
% 3.14/0.99  
% 3.14/0.99  fof(f61,plain,(
% 3.14/0.99    ~r1_tsep_1(sK2,sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f37,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.14/0.99    inference(cnf_transformation,[],[f28])).
% 3.14/0.99  
% 3.14/0.99  fof(f67,plain,(
% 3.14/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.14/0.99    inference(equality_resolution,[],[f37])).
% 3.14/0.99  
% 3.14/0.99  fof(f36,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.14/0.99    inference(cnf_transformation,[],[f28])).
% 3.14/0.99  
% 3.14/0.99  fof(f68,plain,(
% 3.14/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.14/0.99    inference(equality_resolution,[],[f36])).
% 3.14/0.99  
% 3.14/0.99  fof(f44,plain,(
% 3.14/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f29])).
% 3.14/0.99  
% 3.14/0.99  fof(f63,plain,(
% 3.14/0.99    ( ! [X4,X5] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3)) | sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f70,plain,(
% 3.14/0.99    ( ! [X5] : (~m1_subset_1(sK4,u1_struct_0(sK3)) | sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 3.14/0.99    inference(equality_resolution,[],[f63])).
% 3.14/0.99  
% 3.14/0.99  fof(f71,plain,(
% 3.14/0.99    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK2))),
% 3.14/0.99    inference(equality_resolution,[],[f70])).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3,plain,
% 3.14/0.99      ( ~ r2_hidden(X0,X1)
% 3.14/0.99      | r2_hidden(X0,X2)
% 3.14/0.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1248,plain,
% 3.14/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.14/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.14/0.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_19,negated_conjecture,
% 3.14/0.99      ( m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1236,plain,
% 3.14/0.99      ( m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_9,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1242,plain,
% 3.14/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.14/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.14/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1867,plain,
% 3.14/0.99      ( r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top
% 3.14/0.99      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1236,c_1242]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_26,negated_conjecture,
% 3.14/0.99      ( ~ v2_struct_0(sK1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_27,plain,
% 3.14/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_25,negated_conjecture,
% 3.14/0.99      ( l1_pre_topc(sK1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_28,plain,
% 3.14/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_24,negated_conjecture,
% 3.14/0.99      ( ~ v2_struct_0(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_29,plain,
% 3.14/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_23,negated_conjecture,
% 3.14/0.99      ( m1_pre_topc(sK2,sK1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_30,plain,
% 3.14/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_22,negated_conjecture,
% 3.14/0.99      ( ~ v2_struct_0(sK3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_31,plain,
% 3.14/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_21,negated_conjecture,
% 3.14/0.99      ( m1_pre_topc(sK3,sK1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_32,plain,
% 3.14/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_34,plain,
% 3.14/0.99      ( m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1477,plain,
% 3.14/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
% 3.14/0.99      | r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
% 3.14/0.99      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1478,plain,
% 3.14/0.99      ( m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) != iProver_top
% 3.14/0.99      | r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top
% 3.14/0.99      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1477]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10,plain,
% 3.14/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_12,plain,
% 3.14/0.99      ( v2_struct_0(X0)
% 3.14/0.99      | ~ l1_struct_0(X0)
% 3.14/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_287,plain,
% 3.14/0.99      ( v2_struct_0(X0)
% 3.14/0.99      | ~ l1_pre_topc(X0)
% 3.14/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.14/0.99      inference(resolution,[status(thm)],[c_10,c_12]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1548,plain,
% 3.14/0.99      ( v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
% 3.14/0.99      | ~ l1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
% 3.14/0.99      | ~ v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_287]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1549,plain,
% 3.14/0.99      ( v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) = iProver_top
% 3.14/0.99      | l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) != iProver_top
% 3.14/0.99      | v1_xboole_0(u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1548]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_17,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | ~ m1_pre_topc(X2,X1)
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | v2_struct_0(X2)
% 3.14/0.99      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1514,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,sK1)
% 3.14/0.99      | ~ m1_pre_topc(sK2,sK1)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | ~ v2_struct_0(k2_tsep_1(sK1,sK2,X0))
% 3.14/0.99      | v2_struct_0(sK1)
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1588,plain,
% 3.14/0.99      ( ~ m1_pre_topc(sK2,sK1)
% 3.14/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.14/0.99      | ~ v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
% 3.14/0.99      | v2_struct_0(sK1)
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | v2_struct_0(sK3)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1514]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1589,plain,
% 3.14/0.99      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 3.14/0.99      | v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) != iProver_top
% 3.14/0.99      | v2_struct_0(sK1) = iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v2_struct_0(sK3) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_11,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1772,plain,
% 3.14/0.99      ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0)
% 3.14/0.99      | ~ l1_pre_topc(X0)
% 3.14/0.99      | l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1773,plain,
% 3.14/0.99      ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0) != iProver_top
% 3.14/0.99      | l1_pre_topc(X0) != iProver_top
% 3.14/0.99      | l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1772]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1775,plain,
% 3.14/0.99      ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1) != iProver_top
% 3.14/0.99      | l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1773]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_15,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | ~ m1_pre_topc(X2,X1)
% 3.14/0.99      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | v2_struct_0(X2)
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1524,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,sK1)
% 3.14/0.99      | m1_pre_topc(k2_tsep_1(sK1,sK2,X0),sK1)
% 3.14/0.99      | ~ m1_pre_topc(sK2,sK1)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | v2_struct_0(sK1)
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1788,plain,
% 3.14/0.99      ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)
% 3.14/0.99      | ~ m1_pre_topc(sK2,sK1)
% 3.14/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.14/0.99      | v2_struct_0(sK1)
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | v2_struct_0(sK3)
% 3.14/0.99      | ~ l1_pre_topc(sK1) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1524]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1789,plain,
% 3.14/0.99      ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1) = iProver_top
% 3.14/0.99      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.14/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 3.14/0.99      | v2_struct_0(sK1) = iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v2_struct_0(sK3) = iProver_top
% 3.14/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1957,plain,
% 3.14/0.99      ( r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_1867,c_27,c_28,c_29,c_30,c_31,c_32,c_34,c_1478,c_1549,
% 3.14/0.99                 c_1589,c_1775,c_1789]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1233,plain,
% 3.14/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_16,plain,
% 3.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.14/0.99      | ~ m1_pre_topc(X2,X1)
% 3.14/0.99      | v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | v2_struct_0(X0)
% 3.14/0.99      | v2_struct_0(X2)
% 3.14/0.99      | ~ l1_pre_topc(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1239,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.14/0.99      | v1_pre_topc(k2_tsep_1(X1,X0,X2)) = iProver_top
% 3.14/0.99      | v2_struct_0(X1) = iProver_top
% 3.14/0.99      | v2_struct_0(X0) = iProver_top
% 3.14/0.99      | v2_struct_0(X2) = iProver_top
% 3.14/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1240,plain,
% 3.14/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.14/0.99      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1) = iProver_top
% 3.14/0.99      | v2_struct_0(X1) = iProver_top
% 3.14/0.99      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | v2_struct_0(X2) = iProver_top
% 3.14/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_14,plain,
% 3.14/1.00      ( r1_tsep_1(X0,X1)
% 3.14/1.00      | ~ m1_pre_topc(X0,X2)
% 3.14/1.00      | ~ m1_pre_topc(X1,X2)
% 3.14/1.00      | ~ m1_pre_topc(k2_tsep_1(X2,X0,X1),X2)
% 3.14/1.00      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
% 3.14/1.00      | v2_struct_0(X2)
% 3.14/1.00      | v2_struct_0(X0)
% 3.14/1.00      | v2_struct_0(X1)
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 3.14/1.00      | ~ l1_pre_topc(X2)
% 3.14/1.00      | k4_xboole_0(u1_struct_0(X0),k4_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) = u1_struct_0(k2_tsep_1(X2,X0,X1)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_20,negated_conjecture,
% 3.14/1.00      ( ~ r1_tsep_1(sK2,sK3) ),
% 3.14/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_305,plain,
% 3.14/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.14/1.00      | ~ m1_pre_topc(X2,X1)
% 3.14/1.00      | ~ m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 3.14/1.00      | ~ v1_pre_topc(k2_tsep_1(X1,X0,X2))
% 3.14/1.00      | v2_struct_0(X0)
% 3.14/1.00      | v2_struct_0(X2)
% 3.14/1.00      | v2_struct_0(X1)
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X1,X0,X2))
% 3.14/1.00      | ~ l1_pre_topc(X1)
% 3.14/1.00      | k4_xboole_0(u1_struct_0(X0),k4_xboole_0(u1_struct_0(X0),u1_struct_0(X2))) = u1_struct_0(k2_tsep_1(X1,X0,X2))
% 3.14/1.00      | sK2 != X0
% 3.14/1.00      | sK3 != X2 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_306,plain,
% 3.14/1.00      ( ~ m1_pre_topc(k2_tsep_1(X0,sK2,sK3),X0)
% 3.14/1.00      | ~ m1_pre_topc(sK2,X0)
% 3.14/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.14/1.00      | ~ v1_pre_topc(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | v2_struct_0(X0)
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | v2_struct_0(sK2)
% 3.14/1.00      | v2_struct_0(sK3)
% 3.14/1.00      | ~ l1_pre_topc(X0)
% 3.14/1.00      | k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3)) ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_305]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_310,plain,
% 3.14/1.00      ( ~ m1_pre_topc(k2_tsep_1(X0,sK2,sK3),X0)
% 3.14/1.00      | ~ m1_pre_topc(sK2,X0)
% 3.14/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.14/1.00      | ~ v1_pre_topc(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | v2_struct_0(X0)
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | ~ l1_pre_topc(X0)
% 3.14/1.00      | k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3)) ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_306,c_24,c_22]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1228,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | m1_pre_topc(k2_tsep_1(X0,sK2,sK3),X0) != iProver_top
% 3.14/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.14/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.14/1.00      | v1_pre_topc(k2_tsep_1(X0,sK2,sK3)) != iProver_top
% 3.14/1.00      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
% 3.14/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5487,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.14/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.14/1.00      | v1_pre_topc(k2_tsep_1(X0,sK2,sK3)) != iProver_top
% 3.14/1.00      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
% 3.14/1.00      | v2_struct_0(sK2) = iProver_top
% 3.14/1.00      | v2_struct_0(sK3) = iProver_top
% 3.14/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1240,c_1228]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5797,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.14/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.14/1.00      | v1_pre_topc(k2_tsep_1(X0,sK2,sK3)) != iProver_top
% 3.14/1.00      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
% 3.14/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_5487,c_29,c_31]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5810,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.14/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.14/1.00      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
% 3.14/1.00      | v2_struct_0(sK2) = iProver_top
% 3.14/1.00      | v2_struct_0(sK3) = iProver_top
% 3.14/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1239,c_5797]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6072,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.14/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.14/1.00      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) = iProver_top
% 3.14/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_5810,c_29,c_31]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1238,plain,
% 3.14/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.14/1.00      | v2_struct_0(X1) = iProver_top
% 3.14/1.00      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | v2_struct_0(X2) = iProver_top
% 3.14/1.00      | v2_struct_0(k2_tsep_1(X1,X0,X2)) != iProver_top
% 3.14/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6084,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.14/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.14/1.00      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | v2_struct_0(sK2) = iProver_top
% 3.14/1.00      | v2_struct_0(sK3) = iProver_top
% 3.14/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_6072,c_1238]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6089,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(X0,sK2,sK3))
% 3.14/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.14/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.14/1.00      | v2_struct_0(X0) = iProver_top
% 3.14/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_6084,c_29,c_31]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6100,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3))
% 3.14/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 3.14/1.00      | v2_struct_0(sK1) = iProver_top
% 3.14/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1233,c_6089]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_313,plain,
% 3.14/1.00      ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)
% 3.14/1.00      | ~ m1_pre_topc(sK2,sK1)
% 3.14/1.00      | ~ m1_pre_topc(sK3,sK1)
% 3.14/1.00      | ~ v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
% 3.14/1.00      | v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
% 3.14/1.00      | v2_struct_0(sK1)
% 3.14/1.00      | ~ l1_pre_topc(sK1)
% 3.14/1.00      | k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_310]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1504,plain,
% 3.14/1.00      ( ~ m1_pre_topc(X0,sK1)
% 3.14/1.00      | ~ m1_pre_topc(sK2,sK1)
% 3.14/1.00      | v1_pre_topc(k2_tsep_1(sK1,sK2,X0))
% 3.14/1.00      | v2_struct_0(X0)
% 3.14/1.00      | v2_struct_0(sK1)
% 3.14/1.00      | v2_struct_0(sK2)
% 3.14/1.00      | ~ l1_pre_topc(sK1) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1576,plain,
% 3.14/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 3.14/1.00      | ~ m1_pre_topc(sK3,sK1)
% 3.14/1.00      | v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
% 3.14/1.00      | v2_struct_0(sK1)
% 3.14/1.00      | v2_struct_0(sK2)
% 3.14/1.00      | v2_struct_0(sK3)
% 3.14/1.00      | ~ l1_pre_topc(sK1) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_1504]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6117,plain,
% 3.14/1.00      ( k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_6100,c_26,c_25,c_24,c_23,c_22,c_21,c_313,c_1576,
% 3.14/1.00                 c_1588,c_1788]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4,plain,
% 3.14/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1247,plain,
% 3.14/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.14/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6205,plain,
% 3.14/1.00      ( r2_hidden(X0,k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top
% 3.14/1.00      | r2_hidden(X0,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_6117,c_1247]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6312,plain,
% 3.14/1.00      ( r2_hidden(sK4,k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1957,c_6205]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6352,plain,
% 3.14/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top
% 3.14/1.00      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1248,c_6312]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5,plain,
% 3.14/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1246,plain,
% 3.14/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.14/1.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6204,plain,
% 3.14/1.00      ( r2_hidden(X0,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) != iProver_top
% 3.14/1.00      | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_6117,c_1246]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6258,plain,
% 3.14/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1957,c_6204]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6407,plain,
% 3.14/1.00      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_6352,c_6258]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_8,plain,
% 3.14/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.14/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1243,plain,
% 3.14/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.14/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.14/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6412,plain,
% 3.14/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top
% 3.14/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_6407,c_1243]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6305,plain,
% 3.14/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top
% 3.14/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_6258,c_1243]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_18,negated_conjecture,
% 3.14/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.14/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1237,plain,
% 3.14/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.14/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6387,plain,
% 3.14/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.14/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_6305,c_1237]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6419,plain,
% 3.14/1.00      ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.14/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_6412,c_6387]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1229,plain,
% 3.14/1.00      ( v2_struct_0(X0) = iProver_top
% 3.14/1.00      | l1_pre_topc(X0) != iProver_top
% 3.14/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6540,plain,
% 3.14/1.00      ( v2_struct_0(sK2) = iProver_top
% 3.14/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.14/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_6419,c_1229]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1241,plain,
% 3.14/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.14/1.00      | l1_pre_topc(X1) != iProver_top
% 3.14/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1808,plain,
% 3.14/1.00      ( l1_pre_topc(sK1) != iProver_top
% 3.14/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1233,c_1241]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_7198,plain,
% 3.14/1.00      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_6540,c_28,c_29,c_1808]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_7203,plain,
% 3.14/1.00      ( v2_struct_0(sK3) = iProver_top
% 3.14/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_7198,c_1229]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1235,plain,
% 3.14/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1807,plain,
% 3.14/1.00      ( l1_pre_topc(sK1) != iProver_top
% 3.14/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1235,c_1241]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(contradiction,plain,
% 3.14/1.00      ( $false ),
% 3.14/1.00      inference(minisat,[status(thm)],[c_7203,c_1807,c_31,c_28]) ).
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  ------                               Statistics
% 3.14/1.00  
% 3.14/1.00  ------ General
% 3.14/1.00  
% 3.14/1.00  abstr_ref_over_cycles:                  0
% 3.14/1.00  abstr_ref_under_cycles:                 0
% 3.14/1.00  gc_basic_clause_elim:                   0
% 3.14/1.00  forced_gc_time:                         0
% 3.14/1.00  parsing_time:                           0.011
% 3.14/1.00  unif_index_cands_time:                  0.
% 3.14/1.00  unif_index_add_time:                    0.
% 3.14/1.00  orderings_time:                         0.
% 3.14/1.00  out_proof_time:                         0.013
% 3.14/1.00  total_time:                             0.238
% 3.14/1.00  num_of_symbols:                         48
% 3.14/1.00  num_of_terms:                           7569
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing
% 3.14/1.00  
% 3.14/1.00  num_of_splits:                          0
% 3.14/1.00  num_of_split_atoms:                     0
% 3.14/1.00  num_of_reused_defs:                     0
% 3.14/1.00  num_eq_ax_congr_red:                    10
% 3.14/1.00  num_of_sem_filtered_clauses:            1
% 3.14/1.00  num_of_subtypes:                        0
% 3.14/1.00  monotx_restored_types:                  0
% 3.14/1.00  sat_num_of_epr_types:                   0
% 3.14/1.00  sat_num_of_non_cyclic_types:            0
% 3.14/1.00  sat_guarded_non_collapsed_types:        0
% 3.14/1.00  num_pure_diseq_elim:                    0
% 3.14/1.00  simp_replaced_by:                       0
% 3.14/1.00  res_preprocessed:                       127
% 3.14/1.00  prep_upred:                             0
% 3.14/1.00  prep_unflattend:                        6
% 3.14/1.00  smt_new_axioms:                         0
% 3.14/1.00  pred_elim_cands:                        7
% 3.14/1.00  pred_elim:                              2
% 3.14/1.00  pred_elim_cl:                           2
% 3.14/1.00  pred_elim_cycles:                       4
% 3.14/1.00  merged_defs:                            0
% 3.14/1.00  merged_defs_ncl:                        0
% 3.14/1.00  bin_hyper_res:                          0
% 3.14/1.00  prep_cycles:                            4
% 3.14/1.00  pred_elim_time:                         0.009
% 3.14/1.00  splitting_time:                         0.
% 3.14/1.00  sem_filter_time:                        0.
% 3.14/1.00  monotx_time:                            0.001
% 3.14/1.00  subtype_inf_time:                       0.
% 3.14/1.00  
% 3.14/1.00  ------ Problem properties
% 3.14/1.00  
% 3.14/1.00  clauses:                                25
% 3.14/1.00  conjectures:                            8
% 3.14/1.00  epr:                                    11
% 3.14/1.00  horn:                                   14
% 3.14/1.00  ground:                                 8
% 3.14/1.00  unary:                                  7
% 3.14/1.00  binary:                                 3
% 3.14/1.00  lits:                                   82
% 3.14/1.00  lits_eq:                                6
% 3.14/1.00  fd_pure:                                0
% 3.14/1.00  fd_pseudo:                              0
% 3.14/1.00  fd_cond:                                0
% 3.14/1.00  fd_pseudo_cond:                         4
% 3.14/1.00  ac_symbols:                             0
% 3.14/1.00  
% 3.14/1.00  ------ Propositional Solver
% 3.14/1.00  
% 3.14/1.00  prop_solver_calls:                      29
% 3.14/1.00  prop_fast_solver_calls:                 1195
% 3.14/1.00  smt_solver_calls:                       0
% 3.14/1.00  smt_fast_solver_calls:                  0
% 3.14/1.00  prop_num_of_clauses:                    3070
% 3.14/1.00  prop_preprocess_simplified:             7957
% 3.14/1.00  prop_fo_subsumed:                       26
% 3.14/1.00  prop_solver_time:                       0.
% 3.14/1.00  smt_solver_time:                        0.
% 3.14/1.00  smt_fast_solver_time:                   0.
% 3.14/1.00  prop_fast_solver_time:                  0.
% 3.14/1.00  prop_unsat_core_time:                   0.
% 3.14/1.00  
% 3.14/1.00  ------ QBF
% 3.14/1.00  
% 3.14/1.00  qbf_q_res:                              0
% 3.14/1.00  qbf_num_tautologies:                    0
% 3.14/1.00  qbf_prep_cycles:                        0
% 3.14/1.00  
% 3.14/1.00  ------ BMC1
% 3.14/1.00  
% 3.14/1.00  bmc1_current_bound:                     -1
% 3.14/1.00  bmc1_last_solved_bound:                 -1
% 3.14/1.00  bmc1_unsat_core_size:                   -1
% 3.14/1.00  bmc1_unsat_core_parents_size:           -1
% 3.14/1.00  bmc1_merge_next_fun:                    0
% 3.14/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation
% 3.14/1.00  
% 3.14/1.00  inst_num_of_clauses:                    873
% 3.14/1.00  inst_num_in_passive:                    379
% 3.14/1.00  inst_num_in_active:                     312
% 3.14/1.00  inst_num_in_unprocessed:                182
% 3.14/1.00  inst_num_of_loops:                      360
% 3.14/1.00  inst_num_of_learning_restarts:          0
% 3.14/1.00  inst_num_moves_active_passive:          46
% 3.14/1.00  inst_lit_activity:                      0
% 3.14/1.00  inst_lit_activity_moves:                1
% 3.14/1.00  inst_num_tautologies:                   0
% 3.14/1.00  inst_num_prop_implied:                  0
% 3.14/1.00  inst_num_existing_simplified:           0
% 3.14/1.00  inst_num_eq_res_simplified:             0
% 3.14/1.00  inst_num_child_elim:                    0
% 3.14/1.00  inst_num_of_dismatching_blockings:      262
% 3.14/1.00  inst_num_of_non_proper_insts:           339
% 3.14/1.00  inst_num_of_duplicates:                 0
% 3.14/1.00  inst_inst_num_from_inst_to_res:         0
% 3.14/1.00  inst_dismatching_checking_time:         0.
% 3.14/1.00  
% 3.14/1.00  ------ Resolution
% 3.14/1.00  
% 3.14/1.00  res_num_of_clauses:                     0
% 3.14/1.00  res_num_in_passive:                     0
% 3.14/1.00  res_num_in_active:                      0
% 3.14/1.00  res_num_of_loops:                       131
% 3.14/1.00  res_forward_subset_subsumed:            4
% 3.14/1.00  res_backward_subset_subsumed:           0
% 3.14/1.00  res_forward_subsumed:                   0
% 3.14/1.00  res_backward_subsumed:                  0
% 3.14/1.00  res_forward_subsumption_resolution:     0
% 3.14/1.00  res_backward_subsumption_resolution:    0
% 3.14/1.00  res_clause_to_clause_subsumption:       823
% 3.14/1.00  res_orphan_elimination:                 0
% 3.14/1.00  res_tautology_del:                      8
% 3.14/1.00  res_num_eq_res_simplified:              0
% 3.14/1.00  res_num_sel_changes:                    0
% 3.14/1.00  res_moves_from_active_to_pass:          0
% 3.14/1.00  
% 3.14/1.00  ------ Superposition
% 3.14/1.00  
% 3.14/1.00  sup_time_total:                         0.
% 3.14/1.00  sup_time_generating:                    0.
% 3.14/1.00  sup_time_sim_full:                      0.
% 3.14/1.00  sup_time_sim_immed:                     0.
% 3.14/1.00  
% 3.14/1.00  sup_num_of_clauses:                     128
% 3.14/1.00  sup_num_in_active:                      66
% 3.14/1.00  sup_num_in_passive:                     62
% 3.14/1.00  sup_num_of_loops:                       70
% 3.14/1.00  sup_fw_superposition:                   85
% 3.14/1.00  sup_bw_superposition:                   127
% 3.14/1.00  sup_immediate_simplified:               55
% 3.14/1.00  sup_given_eliminated:                   0
% 3.14/1.00  comparisons_done:                       0
% 3.14/1.00  comparisons_avoided:                    0
% 3.14/1.00  
% 3.14/1.00  ------ Simplifications
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  sim_fw_subset_subsumed:                 15
% 3.14/1.00  sim_bw_subset_subsumed:                 1
% 3.14/1.00  sim_fw_subsumed:                        26
% 3.14/1.00  sim_bw_subsumed:                        4
% 3.14/1.00  sim_fw_subsumption_res:                 1
% 3.14/1.00  sim_bw_subsumption_res:                 1
% 3.14/1.00  sim_tautology_del:                      20
% 3.14/1.00  sim_eq_tautology_del:                   3
% 3.14/1.00  sim_eq_res_simp:                        1
% 3.14/1.00  sim_fw_demodulated:                     3
% 3.14/1.00  sim_bw_demodulated:                     5
% 3.14/1.00  sim_light_normalised:                   5
% 3.14/1.00  sim_joinable_taut:                      0
% 3.14/1.00  sim_joinable_simp:                      0
% 3.14/1.00  sim_ac_normalised:                      0
% 3.14/1.00  sim_smt_subsumption:                    0
% 3.14/1.00  
%------------------------------------------------------------------------------

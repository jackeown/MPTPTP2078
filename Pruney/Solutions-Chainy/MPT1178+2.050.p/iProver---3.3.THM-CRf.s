%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:07 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 440 expanded)
%              Number of clauses        :   72 ( 110 expanded)
%              Number of leaves         :   16 ( 118 expanded)
%              Depth                    :   21
%              Number of atoms          :  573 (2552 expanded)
%              Number of equality atoms :  102 ( 413 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,(
    k2_tarski(k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f85,f82])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK6))
        & m1_orders_1(sK6,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK5,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK5))) )
      & l1_orders_2(sK5)
      & v5_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6))
    & m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5)))
    & l1_orders_2(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f52,f66,f65])).

fof(f105,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f67])).

fof(f14,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( m2_orders_2(sK3(X0,X1,X2),X0,X1)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK3(X0,X1,X2),X0,X1)
                    | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f104,plain,(
    m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f67])).

fof(f103,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f99,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f100,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f101,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f102,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f53])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK4(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK4(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f63])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK4(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_15,plain,
    ( k2_tarski(k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1839,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3156,plain,
    ( r2_hidden(k1_xboole_0,X0) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1839])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_14,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1838,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2714,plain,
    ( r1_tarski(k4_orders_2(sK5,sK6),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_1838])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1843,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4974,plain,
    ( r1_xboole_0(k4_orders_2(sK5,sK6),X0) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2714,c_1843])).

cnf(c_24,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_30,negated_conjecture,
    ( m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_591,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_592,plain,
    ( ~ m2_orders_2(X0,X1,sK6)
    | r2_hidden(X0,k4_orders_2(X1,sK6))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_859,plain,
    ( ~ m2_orders_2(X0,X1,sK6)
    | r2_hidden(X0,k4_orders_2(X1,sK6))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_592,c_31])).

cnf(c_860,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | r2_hidden(X0,k4_orders_2(sK5,sK6))
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_34,negated_conjecture,
    ( v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_33,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_864,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | r2_hidden(X0,k4_orders_2(sK5,sK6))
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_860,c_35,c_34,c_33,c_32])).

cnf(c_1014,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | r2_hidden(X0,k4_orders_2(sK5,sK6)) ),
    inference(equality_resolution_simp,[status(thm)],[c_864])).

cnf(c_1079,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | r2_hidden(X0,k4_orders_2(sK5,sK6)) ),
    inference(prop_impl,[status(thm)],[c_1014])).

cnf(c_1829,plain,
    ( m2_orders_2(X0,sK5,sK6) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1849,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5121,plain,
    ( m2_orders_2(X0,sK5,sK6) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1829,c_1849])).

cnf(c_16157,plain,
    ( m2_orders_2(X0,sK5,sK6) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK5,sK6)) != iProver_top
    | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4974,c_5121])).

cnf(c_26,plain,
    ( m2_orders_2(sK4(X0,X1),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_435,plain,
    ( m2_orders_2(sK4(X0,X1),X0,X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_436,plain,
    ( m2_orders_2(sK4(X0,sK6),X0,sK6)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_845,plain,
    ( m2_orders_2(sK4(X0,sK6),X0,sK6)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_436,c_31])).

cnf(c_846,plain,
    ( m2_orders_2(sK4(sK5,sK6),sK5,sK6)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_848,plain,
    ( m2_orders_2(sK4(sK5,sK6),sK5,sK6)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_35,c_34,c_33,c_32])).

cnf(c_1018,plain,
    ( m2_orders_2(sK4(sK5,sK6),sK5,sK6) ),
    inference(equality_resolution_simp,[status(thm)],[c_848])).

cnf(c_1019,plain,
    ( m2_orders_2(sK4(sK5,sK6),sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_2038,plain,
    ( ~ m2_orders_2(sK4(sK5,sK6),sK5,sK6)
    | r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_2039,plain,
    ( m2_orders_2(sK4(sK5,sK6),sK5,sK6) != iProver_top
    | r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2038])).

cnf(c_2140,plain,
    ( ~ r2_hidden(sK4(sK5,sK6),X0)
    | ~ r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6))
    | ~ r1_xboole_0(X0,k4_orders_2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2458,plain,
    ( ~ r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6))
    | ~ r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_2459,plain,
    ( r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6)) != iProver_top
    | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2458])).

cnf(c_2568,plain,
    ( ~ r1_tarski(k4_orders_2(sK5,sK6),X0)
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_orders_2(sK5,sK6),X1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3770,plain,
    ( ~ r1_tarski(k4_orders_2(sK5,sK6),X0)
    | ~ r1_xboole_0(X0,k4_orders_2(sK5,sK6))
    | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2568])).

cnf(c_5221,plain,
    ( ~ r1_tarski(k4_orders_2(sK5,sK6),k1_zfmisc_1(X0))
    | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6))
    | ~ r1_xboole_0(k1_zfmisc_1(X0),k4_orders_2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3770])).

cnf(c_5222,plain,
    ( r1_tarski(k4_orders_2(sK5,sK6),k1_zfmisc_1(X0)) != iProver_top
    | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(X0),k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5221])).

cnf(c_5224,plain,
    ( r1_tarski(k4_orders_2(sK5,sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5222])).

cnf(c_16359,plain,
    ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16157,c_1019,c_2039,c_2459,c_2714,c_5224])).

cnf(c_16364,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_16359])).

cnf(c_25,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_561,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_562,plain,
    ( m2_orders_2(X0,X1,sK6)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK6))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_880,plain,
    ( m2_orders_2(X0,X1,sK6)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK6))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_562,c_31])).

cnf(c_881,plain,
    ( m2_orders_2(X0,sK5,sK6)
    | ~ r2_hidden(X0,k4_orders_2(sK5,sK6))
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_885,plain,
    ( m2_orders_2(X0,sK5,sK6)
    | ~ r2_hidden(X0,k4_orders_2(sK5,sK6))
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_35,c_34,c_33,c_32])).

cnf(c_1010,plain,
    ( m2_orders_2(X0,sK5,sK6)
    | ~ r2_hidden(X0,k4_orders_2(sK5,sK6)) ),
    inference(equality_resolution_simp,[status(thm)],[c_885])).

cnf(c_1011,plain,
    ( m2_orders_2(X0,sK5,sK6) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_1013,plain,
    ( m2_orders_2(k1_xboole_0,sK5,sK6) = iProver_top
    | r2_hidden(k1_xboole_0,k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_28,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_528,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ r1_xboole_0(X3,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_529,plain,
    ( ~ m2_orders_2(X0,X1,sK6)
    | ~ m2_orders_2(X2,X1,sK6)
    | ~ r1_xboole_0(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_901,plain,
    ( ~ m2_orders_2(X0,X1,sK6)
    | ~ m2_orders_2(X2,X1,sK6)
    | ~ r1_xboole_0(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_529,c_31])).

cnf(c_902,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | ~ m2_orders_2(X1,sK5,sK6)
    | ~ r1_xboole_0(X0,X1)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_901])).

cnf(c_906,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | ~ m2_orders_2(X1,sK5,sK6)
    | ~ r1_xboole_0(X0,X1)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_902,c_35,c_34,c_33,c_32])).

cnf(c_1006,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | ~ m2_orders_2(X1,sK5,sK6)
    | ~ r1_xboole_0(X0,X1) ),
    inference(equality_resolution_simp,[status(thm)],[c_906])).

cnf(c_1007,plain,
    ( m2_orders_2(X0,sK5,sK6) != iProver_top
    | m2_orders_2(X1,sK5,sK6) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_1009,plain,
    ( m2_orders_2(k1_xboole_0,sK5,sK6) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_94,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_96,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16364,c_1013,c_1009,c_96])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:35:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.73/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.99  
% 3.73/0.99  ------  iProver source info
% 3.73/0.99  
% 3.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.99  git: non_committed_changes: false
% 3.73/0.99  git: last_make_outside_of_git: false
% 3.73/0.99  
% 3.73/0.99  ------ 
% 3.73/0.99  
% 3.73/0.99  ------ Input Options
% 3.73/0.99  
% 3.73/0.99  --out_options                           all
% 3.73/0.99  --tptp_safe_out                         true
% 3.73/0.99  --problem_path                          ""
% 3.73/0.99  --include_path                          ""
% 3.73/0.99  --clausifier                            res/vclausify_rel
% 3.73/0.99  --clausifier_options                    --mode clausify
% 3.73/0.99  --stdin                                 false
% 3.73/0.99  --stats_out                             all
% 3.73/0.99  
% 3.73/0.99  ------ General Options
% 3.73/0.99  
% 3.73/0.99  --fof                                   false
% 3.73/0.99  --time_out_real                         305.
% 3.73/0.99  --time_out_virtual                      -1.
% 3.73/0.99  --symbol_type_check                     false
% 3.73/0.99  --clausify_out                          false
% 3.73/0.99  --sig_cnt_out                           false
% 3.73/0.99  --trig_cnt_out                          false
% 3.73/0.99  --trig_cnt_out_tolerance                1.
% 3.73/0.99  --trig_cnt_out_sk_spl                   false
% 3.73/0.99  --abstr_cl_out                          false
% 3.73/0.99  
% 3.73/0.99  ------ Global Options
% 3.73/0.99  
% 3.73/0.99  --schedule                              default
% 3.73/0.99  --add_important_lit                     false
% 3.73/0.99  --prop_solver_per_cl                    1000
% 3.73/0.99  --min_unsat_core                        false
% 3.73/0.99  --soft_assumptions                      false
% 3.73/0.99  --soft_lemma_size                       3
% 3.73/0.99  --prop_impl_unit_size                   0
% 3.73/0.99  --prop_impl_unit                        []
% 3.73/0.99  --share_sel_clauses                     true
% 3.73/0.99  --reset_solvers                         false
% 3.73/0.99  --bc_imp_inh                            [conj_cone]
% 3.73/0.99  --conj_cone_tolerance                   3.
% 3.73/0.99  --extra_neg_conj                        none
% 3.73/0.99  --large_theory_mode                     true
% 3.73/0.99  --prolific_symb_bound                   200
% 3.73/0.99  --lt_threshold                          2000
% 3.73/0.99  --clause_weak_htbl                      true
% 3.73/0.99  --gc_record_bc_elim                     false
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing Options
% 3.73/0.99  
% 3.73/0.99  --preprocessing_flag                    true
% 3.73/0.99  --time_out_prep_mult                    0.1
% 3.73/0.99  --splitting_mode                        input
% 3.73/0.99  --splitting_grd                         true
% 3.73/0.99  --splitting_cvd                         false
% 3.73/0.99  --splitting_cvd_svl                     false
% 3.73/0.99  --splitting_nvd                         32
% 3.73/0.99  --sub_typing                            true
% 3.73/0.99  --prep_gs_sim                           true
% 3.73/0.99  --prep_unflatten                        true
% 3.73/0.99  --prep_res_sim                          true
% 3.73/0.99  --prep_upred                            true
% 3.73/0.99  --prep_sem_filter                       exhaustive
% 3.73/0.99  --prep_sem_filter_out                   false
% 3.73/0.99  --pred_elim                             true
% 3.73/0.99  --res_sim_input                         true
% 3.73/0.99  --eq_ax_congr_red                       true
% 3.73/0.99  --pure_diseq_elim                       true
% 3.73/0.99  --brand_transform                       false
% 3.73/0.99  --non_eq_to_eq                          false
% 3.73/0.99  --prep_def_merge                        true
% 3.73/0.99  --prep_def_merge_prop_impl              false
% 3.73/0.99  --prep_def_merge_mbd                    true
% 3.73/0.99  --prep_def_merge_tr_red                 false
% 3.73/0.99  --prep_def_merge_tr_cl                  false
% 3.73/0.99  --smt_preprocessing                     true
% 3.73/0.99  --smt_ac_axioms                         fast
% 3.73/0.99  --preprocessed_out                      false
% 3.73/0.99  --preprocessed_stats                    false
% 3.73/0.99  
% 3.73/0.99  ------ Abstraction refinement Options
% 3.73/0.99  
% 3.73/0.99  --abstr_ref                             []
% 3.73/0.99  --abstr_ref_prep                        false
% 3.73/0.99  --abstr_ref_until_sat                   false
% 3.73/0.99  --abstr_ref_sig_restrict                funpre
% 3.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/0.99  --abstr_ref_under                       []
% 3.73/0.99  
% 3.73/0.99  ------ SAT Options
% 3.73/0.99  
% 3.73/0.99  --sat_mode                              false
% 3.73/0.99  --sat_fm_restart_options                ""
% 3.73/0.99  --sat_gr_def                            false
% 3.73/0.99  --sat_epr_types                         true
% 3.73/0.99  --sat_non_cyclic_types                  false
% 3.73/0.99  --sat_finite_models                     false
% 3.73/0.99  --sat_fm_lemmas                         false
% 3.73/0.99  --sat_fm_prep                           false
% 3.73/0.99  --sat_fm_uc_incr                        true
% 3.73/0.99  --sat_out_model                         small
% 3.73/0.99  --sat_out_clauses                       false
% 3.73/0.99  
% 3.73/0.99  ------ QBF Options
% 3.73/0.99  
% 3.73/0.99  --qbf_mode                              false
% 3.73/0.99  --qbf_elim_univ                         false
% 3.73/0.99  --qbf_dom_inst                          none
% 3.73/0.99  --qbf_dom_pre_inst                      false
% 3.73/0.99  --qbf_sk_in                             false
% 3.73/0.99  --qbf_pred_elim                         true
% 3.73/0.99  --qbf_split                             512
% 3.73/0.99  
% 3.73/0.99  ------ BMC1 Options
% 3.73/0.99  
% 3.73/0.99  --bmc1_incremental                      false
% 3.73/0.99  --bmc1_axioms                           reachable_all
% 3.73/0.99  --bmc1_min_bound                        0
% 3.73/0.99  --bmc1_max_bound                        -1
% 3.73/0.99  --bmc1_max_bound_default                -1
% 3.73/0.99  --bmc1_symbol_reachability              true
% 3.73/0.99  --bmc1_property_lemmas                  false
% 3.73/0.99  --bmc1_k_induction                      false
% 3.73/0.99  --bmc1_non_equiv_states                 false
% 3.73/0.99  --bmc1_deadlock                         false
% 3.73/0.99  --bmc1_ucm                              false
% 3.73/0.99  --bmc1_add_unsat_core                   none
% 3.73/0.99  --bmc1_unsat_core_children              false
% 3.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/0.99  --bmc1_out_stat                         full
% 3.73/0.99  --bmc1_ground_init                      false
% 3.73/0.99  --bmc1_pre_inst_next_state              false
% 3.73/0.99  --bmc1_pre_inst_state                   false
% 3.73/0.99  --bmc1_pre_inst_reach_state             false
% 3.73/0.99  --bmc1_out_unsat_core                   false
% 3.73/0.99  --bmc1_aig_witness_out                  false
% 3.73/0.99  --bmc1_verbose                          false
% 3.73/0.99  --bmc1_dump_clauses_tptp                false
% 3.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.73/0.99  --bmc1_dump_file                        -
% 3.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.73/0.99  --bmc1_ucm_extend_mode                  1
% 3.73/0.99  --bmc1_ucm_init_mode                    2
% 3.73/0.99  --bmc1_ucm_cone_mode                    none
% 3.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.73/0.99  --bmc1_ucm_relax_model                  4
% 3.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/0.99  --bmc1_ucm_layered_model                none
% 3.73/0.99  --bmc1_ucm_max_lemma_size               10
% 3.73/0.99  
% 3.73/0.99  ------ AIG Options
% 3.73/0.99  
% 3.73/0.99  --aig_mode                              false
% 3.73/0.99  
% 3.73/0.99  ------ Instantiation Options
% 3.73/0.99  
% 3.73/0.99  --instantiation_flag                    true
% 3.73/0.99  --inst_sos_flag                         false
% 3.73/0.99  --inst_sos_phase                        true
% 3.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/0.99  --inst_lit_sel_side                     num_symb
% 3.73/0.99  --inst_solver_per_active                1400
% 3.73/0.99  --inst_solver_calls_frac                1.
% 3.73/0.99  --inst_passive_queue_type               priority_queues
% 3.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/0.99  --inst_passive_queues_freq              [25;2]
% 3.73/0.99  --inst_dismatching                      true
% 3.73/0.99  --inst_eager_unprocessed_to_passive     true
% 3.73/0.99  --inst_prop_sim_given                   true
% 3.73/0.99  --inst_prop_sim_new                     false
% 3.73/0.99  --inst_subs_new                         false
% 3.73/0.99  --inst_eq_res_simp                      false
% 3.73/0.99  --inst_subs_given                       false
% 3.73/0.99  --inst_orphan_elimination               true
% 3.73/0.99  --inst_learning_loop_flag               true
% 3.73/0.99  --inst_learning_start                   3000
% 3.73/0.99  --inst_learning_factor                  2
% 3.73/0.99  --inst_start_prop_sim_after_learn       3
% 3.73/0.99  --inst_sel_renew                        solver
% 3.73/0.99  --inst_lit_activity_flag                true
% 3.73/0.99  --inst_restr_to_given                   false
% 3.73/0.99  --inst_activity_threshold               500
% 3.73/0.99  --inst_out_proof                        true
% 3.73/0.99  
% 3.73/0.99  ------ Resolution Options
% 3.73/0.99  
% 3.73/0.99  --resolution_flag                       true
% 3.73/0.99  --res_lit_sel                           adaptive
% 3.73/0.99  --res_lit_sel_side                      none
% 3.73/0.99  --res_ordering                          kbo
% 3.73/0.99  --res_to_prop_solver                    active
% 3.73/0.99  --res_prop_simpl_new                    false
% 3.73/0.99  --res_prop_simpl_given                  true
% 3.73/0.99  --res_passive_queue_type                priority_queues
% 3.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/0.99  --res_passive_queues_freq               [15;5]
% 3.73/0.99  --res_forward_subs                      full
% 3.73/0.99  --res_backward_subs                     full
% 3.73/0.99  --res_forward_subs_resolution           true
% 3.73/0.99  --res_backward_subs_resolution          true
% 3.73/0.99  --res_orphan_elimination                true
% 3.73/0.99  --res_time_limit                        2.
% 3.73/0.99  --res_out_proof                         true
% 3.73/0.99  
% 3.73/0.99  ------ Superposition Options
% 3.73/0.99  
% 3.73/0.99  --superposition_flag                    true
% 3.73/0.99  --sup_passive_queue_type                priority_queues
% 3.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.73/0.99  --demod_completeness_check              fast
% 3.73/0.99  --demod_use_ground                      true
% 3.73/0.99  --sup_to_prop_solver                    passive
% 3.73/0.99  --sup_prop_simpl_new                    true
% 3.73/0.99  --sup_prop_simpl_given                  true
% 3.73/0.99  --sup_fun_splitting                     false
% 3.73/0.99  --sup_smt_interval                      50000
% 3.73/0.99  
% 3.73/0.99  ------ Superposition Simplification Setup
% 3.73/0.99  
% 3.73/0.99  --sup_indices_passive                   []
% 3.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_full_bw                           [BwDemod]
% 3.73/0.99  --sup_immed_triv                        [TrivRules]
% 3.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_immed_bw_main                     []
% 3.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.99  
% 3.73/0.99  ------ Combination Options
% 3.73/0.99  
% 3.73/0.99  --comb_res_mult                         3
% 3.73/0.99  --comb_sup_mult                         2
% 3.73/0.99  --comb_inst_mult                        10
% 3.73/0.99  
% 3.73/0.99  ------ Debug Options
% 3.73/0.99  
% 3.73/0.99  --dbg_backtrace                         false
% 3.73/0.99  --dbg_dump_prop_clauses                 false
% 3.73/0.99  --dbg_dump_prop_clauses_file            -
% 3.73/0.99  --dbg_out_stat                          false
% 3.73/0.99  ------ Parsing...
% 3.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  ------ Proving...
% 3.73/0.99  ------ Problem Properties 
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  clauses                                 29
% 3.73/0.99  conjectures                             1
% 3.73/0.99  EPR                                     5
% 3.73/0.99  Horn                                    23
% 3.73/0.99  unary                                   12
% 3.73/0.99  binary                                  8
% 3.73/0.99  lits                                    56
% 3.73/0.99  lits eq                                 9
% 3.73/0.99  fd_pure                                 0
% 3.73/0.99  fd_pseudo                               0
% 3.73/0.99  fd_cond                                 2
% 3.73/0.99  fd_pseudo_cond                          1
% 3.73/0.99  AC symbols                              0
% 3.73/0.99  
% 3.73/0.99  ------ Schedule dynamic 5 is on 
% 3.73/0.99  
% 3.73/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ 
% 3.73/0.99  Current options:
% 3.73/0.99  ------ 
% 3.73/0.99  
% 3.73/0.99  ------ Input Options
% 3.73/0.99  
% 3.73/0.99  --out_options                           all
% 3.73/0.99  --tptp_safe_out                         true
% 3.73/0.99  --problem_path                          ""
% 3.73/0.99  --include_path                          ""
% 3.73/0.99  --clausifier                            res/vclausify_rel
% 3.73/0.99  --clausifier_options                    --mode clausify
% 3.73/0.99  --stdin                                 false
% 3.73/0.99  --stats_out                             all
% 3.73/0.99  
% 3.73/0.99  ------ General Options
% 3.73/0.99  
% 3.73/0.99  --fof                                   false
% 3.73/0.99  --time_out_real                         305.
% 3.73/0.99  --time_out_virtual                      -1.
% 3.73/0.99  --symbol_type_check                     false
% 3.73/0.99  --clausify_out                          false
% 3.73/0.99  --sig_cnt_out                           false
% 3.73/0.99  --trig_cnt_out                          false
% 3.73/0.99  --trig_cnt_out_tolerance                1.
% 3.73/0.99  --trig_cnt_out_sk_spl                   false
% 3.73/0.99  --abstr_cl_out                          false
% 3.73/0.99  
% 3.73/0.99  ------ Global Options
% 3.73/0.99  
% 3.73/0.99  --schedule                              default
% 3.73/0.99  --add_important_lit                     false
% 3.73/0.99  --prop_solver_per_cl                    1000
% 3.73/0.99  --min_unsat_core                        false
% 3.73/0.99  --soft_assumptions                      false
% 3.73/0.99  --soft_lemma_size                       3
% 3.73/0.99  --prop_impl_unit_size                   0
% 3.73/0.99  --prop_impl_unit                        []
% 3.73/0.99  --share_sel_clauses                     true
% 3.73/0.99  --reset_solvers                         false
% 3.73/0.99  --bc_imp_inh                            [conj_cone]
% 3.73/0.99  --conj_cone_tolerance                   3.
% 3.73/0.99  --extra_neg_conj                        none
% 3.73/0.99  --large_theory_mode                     true
% 3.73/0.99  --prolific_symb_bound                   200
% 3.73/0.99  --lt_threshold                          2000
% 3.73/0.99  --clause_weak_htbl                      true
% 3.73/0.99  --gc_record_bc_elim                     false
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing Options
% 3.73/0.99  
% 3.73/0.99  --preprocessing_flag                    true
% 3.73/0.99  --time_out_prep_mult                    0.1
% 3.73/0.99  --splitting_mode                        input
% 3.73/0.99  --splitting_grd                         true
% 3.73/0.99  --splitting_cvd                         false
% 3.73/0.99  --splitting_cvd_svl                     false
% 3.73/0.99  --splitting_nvd                         32
% 3.73/0.99  --sub_typing                            true
% 3.73/0.99  --prep_gs_sim                           true
% 3.73/0.99  --prep_unflatten                        true
% 3.73/0.99  --prep_res_sim                          true
% 3.73/0.99  --prep_upred                            true
% 3.73/0.99  --prep_sem_filter                       exhaustive
% 3.73/0.99  --prep_sem_filter_out                   false
% 3.73/0.99  --pred_elim                             true
% 3.73/0.99  --res_sim_input                         true
% 3.73/0.99  --eq_ax_congr_red                       true
% 3.73/0.99  --pure_diseq_elim                       true
% 3.73/0.99  --brand_transform                       false
% 3.73/0.99  --non_eq_to_eq                          false
% 3.73/0.99  --prep_def_merge                        true
% 3.73/0.99  --prep_def_merge_prop_impl              false
% 3.73/0.99  --prep_def_merge_mbd                    true
% 3.73/0.99  --prep_def_merge_tr_red                 false
% 3.73/0.99  --prep_def_merge_tr_cl                  false
% 3.73/0.99  --smt_preprocessing                     true
% 3.73/0.99  --smt_ac_axioms                         fast
% 3.73/0.99  --preprocessed_out                      false
% 3.73/0.99  --preprocessed_stats                    false
% 3.73/0.99  
% 3.73/0.99  ------ Abstraction refinement Options
% 3.73/0.99  
% 3.73/0.99  --abstr_ref                             []
% 3.73/0.99  --abstr_ref_prep                        false
% 3.73/0.99  --abstr_ref_until_sat                   false
% 3.73/0.99  --abstr_ref_sig_restrict                funpre
% 3.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/0.99  --abstr_ref_under                       []
% 3.73/0.99  
% 3.73/0.99  ------ SAT Options
% 3.73/0.99  
% 3.73/0.99  --sat_mode                              false
% 3.73/0.99  --sat_fm_restart_options                ""
% 3.73/0.99  --sat_gr_def                            false
% 3.73/0.99  --sat_epr_types                         true
% 3.73/0.99  --sat_non_cyclic_types                  false
% 3.73/0.99  --sat_finite_models                     false
% 3.73/0.99  --sat_fm_lemmas                         false
% 3.73/0.99  --sat_fm_prep                           false
% 3.73/0.99  --sat_fm_uc_incr                        true
% 3.73/0.99  --sat_out_model                         small
% 3.73/0.99  --sat_out_clauses                       false
% 3.73/0.99  
% 3.73/0.99  ------ QBF Options
% 3.73/0.99  
% 3.73/0.99  --qbf_mode                              false
% 3.73/0.99  --qbf_elim_univ                         false
% 3.73/0.99  --qbf_dom_inst                          none
% 3.73/0.99  --qbf_dom_pre_inst                      false
% 3.73/0.99  --qbf_sk_in                             false
% 3.73/0.99  --qbf_pred_elim                         true
% 3.73/0.99  --qbf_split                             512
% 3.73/0.99  
% 3.73/0.99  ------ BMC1 Options
% 3.73/0.99  
% 3.73/0.99  --bmc1_incremental                      false
% 3.73/0.99  --bmc1_axioms                           reachable_all
% 3.73/0.99  --bmc1_min_bound                        0
% 3.73/0.99  --bmc1_max_bound                        -1
% 3.73/0.99  --bmc1_max_bound_default                -1
% 3.73/0.99  --bmc1_symbol_reachability              true
% 3.73/0.99  --bmc1_property_lemmas                  false
% 3.73/0.99  --bmc1_k_induction                      false
% 3.73/0.99  --bmc1_non_equiv_states                 false
% 3.73/0.99  --bmc1_deadlock                         false
% 3.73/0.99  --bmc1_ucm                              false
% 3.73/0.99  --bmc1_add_unsat_core                   none
% 3.73/0.99  --bmc1_unsat_core_children              false
% 3.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/0.99  --bmc1_out_stat                         full
% 3.73/0.99  --bmc1_ground_init                      false
% 3.73/0.99  --bmc1_pre_inst_next_state              false
% 3.73/0.99  --bmc1_pre_inst_state                   false
% 3.73/0.99  --bmc1_pre_inst_reach_state             false
% 3.73/0.99  --bmc1_out_unsat_core                   false
% 3.73/0.99  --bmc1_aig_witness_out                  false
% 3.73/0.99  --bmc1_verbose                          false
% 3.73/0.99  --bmc1_dump_clauses_tptp                false
% 3.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.73/0.99  --bmc1_dump_file                        -
% 3.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.73/0.99  --bmc1_ucm_extend_mode                  1
% 3.73/0.99  --bmc1_ucm_init_mode                    2
% 3.73/0.99  --bmc1_ucm_cone_mode                    none
% 3.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.73/0.99  --bmc1_ucm_relax_model                  4
% 3.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/0.99  --bmc1_ucm_layered_model                none
% 3.73/0.99  --bmc1_ucm_max_lemma_size               10
% 3.73/0.99  
% 3.73/0.99  ------ AIG Options
% 3.73/0.99  
% 3.73/0.99  --aig_mode                              false
% 3.73/0.99  
% 3.73/0.99  ------ Instantiation Options
% 3.73/0.99  
% 3.73/0.99  --instantiation_flag                    true
% 3.73/0.99  --inst_sos_flag                         false
% 3.73/0.99  --inst_sos_phase                        true
% 3.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/0.99  --inst_lit_sel_side                     none
% 3.73/0.99  --inst_solver_per_active                1400
% 3.73/0.99  --inst_solver_calls_frac                1.
% 3.73/0.99  --inst_passive_queue_type               priority_queues
% 3.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/0.99  --inst_passive_queues_freq              [25;2]
% 3.73/0.99  --inst_dismatching                      true
% 3.73/0.99  --inst_eager_unprocessed_to_passive     true
% 3.73/0.99  --inst_prop_sim_given                   true
% 3.73/0.99  --inst_prop_sim_new                     false
% 3.73/0.99  --inst_subs_new                         false
% 3.73/0.99  --inst_eq_res_simp                      false
% 3.73/0.99  --inst_subs_given                       false
% 3.73/0.99  --inst_orphan_elimination               true
% 3.73/0.99  --inst_learning_loop_flag               true
% 3.73/0.99  --inst_learning_start                   3000
% 3.73/0.99  --inst_learning_factor                  2
% 3.73/0.99  --inst_start_prop_sim_after_learn       3
% 3.73/0.99  --inst_sel_renew                        solver
% 3.73/0.99  --inst_lit_activity_flag                true
% 3.73/0.99  --inst_restr_to_given                   false
% 3.73/0.99  --inst_activity_threshold               500
% 3.73/0.99  --inst_out_proof                        true
% 3.73/0.99  
% 3.73/0.99  ------ Resolution Options
% 3.73/0.99  
% 3.73/0.99  --resolution_flag                       false
% 3.73/0.99  --res_lit_sel                           adaptive
% 3.73/0.99  --res_lit_sel_side                      none
% 3.73/0.99  --res_ordering                          kbo
% 3.73/0.99  --res_to_prop_solver                    active
% 3.73/0.99  --res_prop_simpl_new                    false
% 3.73/0.99  --res_prop_simpl_given                  true
% 3.73/0.99  --res_passive_queue_type                priority_queues
% 3.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/0.99  --res_passive_queues_freq               [15;5]
% 3.73/0.99  --res_forward_subs                      full
% 3.73/0.99  --res_backward_subs                     full
% 3.73/0.99  --res_forward_subs_resolution           true
% 3.73/0.99  --res_backward_subs_resolution          true
% 3.73/0.99  --res_orphan_elimination                true
% 3.73/0.99  --res_time_limit                        2.
% 3.73/0.99  --res_out_proof                         true
% 3.73/0.99  
% 3.73/0.99  ------ Superposition Options
% 3.73/0.99  
% 3.73/0.99  --superposition_flag                    true
% 3.73/0.99  --sup_passive_queue_type                priority_queues
% 3.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.73/0.99  --demod_completeness_check              fast
% 3.73/0.99  --demod_use_ground                      true
% 3.73/0.99  --sup_to_prop_solver                    passive
% 3.73/0.99  --sup_prop_simpl_new                    true
% 3.73/0.99  --sup_prop_simpl_given                  true
% 3.73/0.99  --sup_fun_splitting                     false
% 3.73/0.99  --sup_smt_interval                      50000
% 3.73/0.99  
% 3.73/0.99  ------ Superposition Simplification Setup
% 3.73/0.99  
% 3.73/0.99  --sup_indices_passive                   []
% 3.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_full_bw                           [BwDemod]
% 3.73/0.99  --sup_immed_triv                        [TrivRules]
% 3.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_immed_bw_main                     []
% 3.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.99  
% 3.73/0.99  ------ Combination Options
% 3.73/0.99  
% 3.73/0.99  --comb_res_mult                         3
% 3.73/0.99  --comb_sup_mult                         2
% 3.73/0.99  --comb_inst_mult                        10
% 3.73/0.99  
% 3.73/0.99  ------ Debug Options
% 3.73/0.99  
% 3.73/0.99  --dbg_backtrace                         false
% 3.73/0.99  --dbg_dump_prop_clauses                 false
% 3.73/0.99  --dbg_dump_prop_clauses_file            -
% 3.73/0.99  --dbg_out_stat                          false
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  % SZS status Theorem for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  fof(f15,axiom,(
% 3.73/0.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f85,plain,(
% 3.73/0.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.73/0.99    inference(cnf_transformation,[],[f15])).
% 3.73/0.99  
% 3.73/0.99  fof(f12,axiom,(
% 3.73/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f82,plain,(
% 3.73/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f12])).
% 3.73/0.99  
% 3.73/0.99  fof(f109,plain,(
% 3.73/0.99    k2_tarski(k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.73/0.99    inference(definition_unfolding,[],[f85,f82])).
% 3.73/0.99  
% 3.73/0.99  fof(f13,axiom,(
% 3.73/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f37,plain,(
% 3.73/0.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.73/0.99    inference(ennf_transformation,[],[f13])).
% 3.73/0.99  
% 3.73/0.99  fof(f83,plain,(
% 3.73/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f37])).
% 3.73/0.99  
% 3.73/0.99  fof(f108,plain,(
% 3.73/0.99    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.73/0.99    inference(definition_unfolding,[],[f83,f82])).
% 3.73/0.99  
% 3.73/0.99  fof(f25,conjecture,(
% 3.73/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f26,negated_conjecture,(
% 3.73/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 3.73/0.99    inference(negated_conjecture,[],[f25])).
% 3.73/0.99  
% 3.73/0.99  fof(f51,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f26])).
% 3.73/0.99  
% 3.73/0.99  fof(f52,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.73/0.99    inference(flattening,[],[f51])).
% 3.73/0.99  
% 3.73/0.99  fof(f66,plain,(
% 3.73/0.99    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK6)) & m1_orders_1(sK6,k1_orders_1(u1_struct_0(X0))))) )),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f65,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK5,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK5)))) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f67,plain,(
% 3.73/0.99    (k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6)) & m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5)))) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5)),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f52,f66,f65])).
% 3.73/0.99  
% 3.73/0.99  fof(f105,plain,(
% 3.73/0.99    k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6))),
% 3.73/0.99    inference(cnf_transformation,[],[f67])).
% 3.73/0.99  
% 3.73/0.99  fof(f14,axiom,(
% 3.73/0.99    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f84,plain,(
% 3.73/0.99    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f14])).
% 3.73/0.99  
% 3.73/0.99  fof(f7,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f31,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.73/0.99    inference(ennf_transformation,[],[f7])).
% 3.73/0.99  
% 3.73/0.99  fof(f32,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.73/0.99    inference(flattening,[],[f31])).
% 3.73/0.99  
% 3.73/0.99  fof(f77,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f32])).
% 3.73/0.99  
% 3.73/0.99  fof(f21,axiom,(
% 3.73/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f43,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f21])).
% 3.73/0.99  
% 3.73/0.99  fof(f44,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.99    inference(flattening,[],[f43])).
% 3.73/0.99  
% 3.73/0.99  fof(f59,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.99    inference(nnf_transformation,[],[f44])).
% 3.73/0.99  
% 3.73/0.99  fof(f60,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.99    inference(rectify,[],[f59])).
% 3.73/0.99  
% 3.73/0.99  fof(f61,plain,(
% 3.73/0.99    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f62,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).
% 3.73/0.99  
% 3.73/0.99  fof(f93,plain,(
% 3.73/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f62])).
% 3.73/0.99  
% 3.73/0.99  fof(f111,plain,(
% 3.73/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.99    inference(equality_resolution,[],[f93])).
% 3.73/0.99  
% 3.73/0.99  fof(f104,plain,(
% 3.73/0.99    m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5)))),
% 3.73/0.99    inference(cnf_transformation,[],[f67])).
% 3.73/0.99  
% 3.73/0.99  fof(f103,plain,(
% 3.73/0.99    l1_orders_2(sK5)),
% 3.73/0.99    inference(cnf_transformation,[],[f67])).
% 3.73/0.99  
% 3.73/0.99  fof(f99,plain,(
% 3.73/0.99    ~v2_struct_0(sK5)),
% 3.73/0.99    inference(cnf_transformation,[],[f67])).
% 3.73/0.99  
% 3.73/0.99  fof(f100,plain,(
% 3.73/0.99    v3_orders_2(sK5)),
% 3.73/0.99    inference(cnf_transformation,[],[f67])).
% 3.73/0.99  
% 3.73/0.99  fof(f101,plain,(
% 3.73/0.99    v4_orders_2(sK5)),
% 3.73/0.99    inference(cnf_transformation,[],[f67])).
% 3.73/0.99  
% 3.73/0.99  fof(f102,plain,(
% 3.73/0.99    v5_orders_2(sK5)),
% 3.73/0.99    inference(cnf_transformation,[],[f67])).
% 3.73/0.99  
% 3.73/0.99  fof(f1,axiom,(
% 3.73/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f27,plain,(
% 3.73/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.73/0.99    inference(rectify,[],[f1])).
% 3.73/0.99  
% 3.73/0.99  fof(f29,plain,(
% 3.73/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.73/0.99    inference(ennf_transformation,[],[f27])).
% 3.73/0.99  
% 3.73/0.99  fof(f53,plain,(
% 3.73/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f54,plain,(
% 3.73/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f70,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f54])).
% 3.73/0.99  
% 3.73/0.99  fof(f22,axiom,(
% 3.73/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f45,plain,(
% 3.73/0.99    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f22])).
% 3.73/0.99  
% 3.73/0.99  fof(f46,plain,(
% 3.73/0.99    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.99    inference(flattening,[],[f45])).
% 3.73/0.99  
% 3.73/0.99  fof(f63,plain,(
% 3.73/0.99    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK4(X0,X1),X0,X1))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f64,plain,(
% 3.73/0.99    ! [X0,X1] : (m2_orders_2(sK4(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f63])).
% 3.73/0.99  
% 3.73/0.99  fof(f96,plain,(
% 3.73/0.99    ( ! [X0,X1] : (m2_orders_2(sK4(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f64])).
% 3.73/0.99  
% 3.73/0.99  fof(f92,plain,(
% 3.73/0.99    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f62])).
% 3.73/0.99  
% 3.73/0.99  fof(f112,plain,(
% 3.73/0.99    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.99    inference(equality_resolution,[],[f92])).
% 3.73/0.99  
% 3.73/0.99  fof(f24,axiom,(
% 3.73/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f49,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f24])).
% 3.73/0.99  
% 3.73/0.99  fof(f50,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.99    inference(flattening,[],[f49])).
% 3.73/0.99  
% 3.73/0.99  fof(f98,plain,(
% 3.73/0.99    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f50])).
% 3.73/0.99  
% 3.73/0.99  fof(f8,axiom,(
% 3.73/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f78,plain,(
% 3.73/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f8])).
% 3.73/0.99  
% 3.73/0.99  cnf(c_15,plain,
% 3.73/0.99      ( k2_tarski(k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_13,plain,
% 3.73/0.99      ( r2_hidden(X0,X1) | r1_xboole_0(k2_tarski(X0,X0),X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1839,plain,
% 3.73/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.73/0.99      | r1_xboole_0(k2_tarski(X0,X0),X1) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3156,plain,
% 3.73/0.99      ( r2_hidden(k1_xboole_0,X0) = iProver_top
% 3.73/0.99      | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_15,c_1839]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_29,negated_conjecture,
% 3.73/0.99      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_14,plain,
% 3.73/0.99      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
% 3.73/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1838,plain,
% 3.73/0.99      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2714,plain,
% 3.73/0.99      ( r1_tarski(k4_orders_2(sK5,sK6),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_29,c_1838]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_8,plain,
% 3.73/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 3.73/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1843,plain,
% 3.73/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.73/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.73/0.99      | r1_xboole_0(X0,X2) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4974,plain,
% 3.73/0.99      ( r1_xboole_0(k4_orders_2(sK5,sK6),X0) = iProver_top
% 3.73/0.99      | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_2714,c_1843]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_24,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 3.73/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(X1,X2))
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_30,negated_conjecture,
% 3.73/0.99      ( m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5))) ),
% 3.73/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_591,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(X1,X2))
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 3.73/0.99      | sK6 != X2 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_592,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,X1,sK6)
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(X1,sK6))
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_591]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_31,negated_conjecture,
% 3.73/0.99      ( l1_orders_2(sK5) ),
% 3.73/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_859,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,X1,sK6)
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(X1,sK6))
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 3.73/0.99      | sK5 != X1 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_592,c_31]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_860,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,sK5,sK6)
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(sK5,sK6))
% 3.73/0.99      | v2_struct_0(sK5)
% 3.73/0.99      | ~ v3_orders_2(sK5)
% 3.73/0.99      | ~ v4_orders_2(sK5)
% 3.73/0.99      | ~ v5_orders_2(sK5)
% 3.73/0.99      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_859]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_35,negated_conjecture,
% 3.73/0.99      ( ~ v2_struct_0(sK5) ),
% 3.73/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_34,negated_conjecture,
% 3.73/0.99      ( v3_orders_2(sK5) ),
% 3.73/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_33,negated_conjecture,
% 3.73/0.99      ( v4_orders_2(sK5) ),
% 3.73/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_32,negated_conjecture,
% 3.73/0.99      ( v5_orders_2(sK5) ),
% 3.73/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_864,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,sK5,sK6)
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(sK5,sK6))
% 3.73/0.99      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_860,c_35,c_34,c_33,c_32]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1014,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,sK5,sK6) | r2_hidden(X0,k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(equality_resolution_simp,[status(thm)],[c_864]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1079,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,sK5,sK6) | r2_hidden(X0,k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(prop_impl,[status(thm)],[c_1014]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1829,plain,
% 3.73/0.99      ( m2_orders_2(X0,sK5,sK6) != iProver_top
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(sK5,sK6)) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_0,plain,
% 3.73/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1849,plain,
% 3.73/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.73/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.73/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5121,plain,
% 3.73/0.99      ( m2_orders_2(X0,sK5,sK6) != iProver_top
% 3.73/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.73/0.99      | r1_xboole_0(X1,k4_orders_2(sK5,sK6)) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1829,c_1849]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16157,plain,
% 3.73/0.99      ( m2_orders_2(X0,sK5,sK6) != iProver_top
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(sK5,sK6)) != iProver_top
% 3.73/0.99      | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_orders_2(sK5,sK6)) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_4974,c_5121]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_26,plain,
% 3.73/0.99      ( m2_orders_2(sK4(X0,X1),X0,X1)
% 3.73/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 3.73/0.99      | v2_struct_0(X0)
% 3.73/0.99      | ~ v3_orders_2(X0)
% 3.73/0.99      | ~ v4_orders_2(X0)
% 3.73/0.99      | ~ v5_orders_2(X0)
% 3.73/0.99      | ~ l1_orders_2(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_435,plain,
% 3.73/0.99      ( m2_orders_2(sK4(X0,X1),X0,X1)
% 3.73/0.99      | v2_struct_0(X0)
% 3.73/0.99      | ~ v3_orders_2(X0)
% 3.73/0.99      | ~ v4_orders_2(X0)
% 3.73/0.99      | ~ v5_orders_2(X0)
% 3.73/0.99      | ~ l1_orders_2(X0)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5))
% 3.73/0.99      | sK6 != X1 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_436,plain,
% 3.73/0.99      ( m2_orders_2(sK4(X0,sK6),X0,sK6)
% 3.73/0.99      | v2_struct_0(X0)
% 3.73/0.99      | ~ v3_orders_2(X0)
% 3.73/0.99      | ~ v4_orders_2(X0)
% 3.73/0.99      | ~ v5_orders_2(X0)
% 3.73/0.99      | ~ l1_orders_2(X0)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_435]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_845,plain,
% 3.73/0.99      ( m2_orders_2(sK4(X0,sK6),X0,sK6)
% 3.73/0.99      | v2_struct_0(X0)
% 3.73/0.99      | ~ v3_orders_2(X0)
% 3.73/0.99      | ~ v4_orders_2(X0)
% 3.73/0.99      | ~ v5_orders_2(X0)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5))
% 3.73/0.99      | sK5 != X0 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_436,c_31]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_846,plain,
% 3.73/0.99      ( m2_orders_2(sK4(sK5,sK6),sK5,sK6)
% 3.73/0.99      | v2_struct_0(sK5)
% 3.73/0.99      | ~ v3_orders_2(sK5)
% 3.73/0.99      | ~ v4_orders_2(sK5)
% 3.73/0.99      | ~ v5_orders_2(sK5)
% 3.73/0.99      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_845]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_848,plain,
% 3.73/0.99      ( m2_orders_2(sK4(sK5,sK6),sK5,sK6)
% 3.73/0.99      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_846,c_35,c_34,c_33,c_32]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1018,plain,
% 3.73/0.99      ( m2_orders_2(sK4(sK5,sK6),sK5,sK6) ),
% 3.73/0.99      inference(equality_resolution_simp,[status(thm)],[c_848]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1019,plain,
% 3.73/0.99      ( m2_orders_2(sK4(sK5,sK6),sK5,sK6) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2038,plain,
% 3.73/0.99      ( ~ m2_orders_2(sK4(sK5,sK6),sK5,sK6)
% 3.73/0.99      | r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_1079]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2039,plain,
% 3.73/0.99      ( m2_orders_2(sK4(sK5,sK6),sK5,sK6) != iProver_top
% 3.73/0.99      | r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6)) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2038]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2140,plain,
% 3.73/0.99      ( ~ r2_hidden(sK4(sK5,sK6),X0)
% 3.73/0.99      | ~ r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6))
% 3.73/0.99      | ~ r1_xboole_0(X0,k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2458,plain,
% 3.73/0.99      ( ~ r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6))
% 3.73/0.99      | ~ r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_2140]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2459,plain,
% 3.73/0.99      ( r2_hidden(sK4(sK5,sK6),k4_orders_2(sK5,sK6)) != iProver_top
% 3.73/0.99      | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2458]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2568,plain,
% 3.73/0.99      ( ~ r1_tarski(k4_orders_2(sK5,sK6),X0)
% 3.73/0.99      | ~ r1_xboole_0(X0,X1)
% 3.73/0.99      | r1_xboole_0(k4_orders_2(sK5,sK6),X1) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3770,plain,
% 3.73/0.99      ( ~ r1_tarski(k4_orders_2(sK5,sK6),X0)
% 3.73/0.99      | ~ r1_xboole_0(X0,k4_orders_2(sK5,sK6))
% 3.73/0.99      | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_2568]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5221,plain,
% 3.73/0.99      ( ~ r1_tarski(k4_orders_2(sK5,sK6),k1_zfmisc_1(X0))
% 3.73/0.99      | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6))
% 3.73/0.99      | ~ r1_xboole_0(k1_zfmisc_1(X0),k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_3770]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5222,plain,
% 3.73/0.99      ( r1_tarski(k4_orders_2(sK5,sK6),k1_zfmisc_1(X0)) != iProver_top
% 3.73/0.99      | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) = iProver_top
% 3.73/0.99      | r1_xboole_0(k1_zfmisc_1(X0),k4_orders_2(sK5,sK6)) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_5221]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5224,plain,
% 3.73/0.99      ( r1_tarski(k4_orders_2(sK5,sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.73/0.99      | r1_xboole_0(k4_orders_2(sK5,sK6),k4_orders_2(sK5,sK6)) = iProver_top
% 3.73/0.99      | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_orders_2(sK5,sK6)) != iProver_top ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_5222]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16359,plain,
% 3.73/0.99      ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k4_orders_2(sK5,sK6)) != iProver_top ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_16157,c_1019,c_2039,c_2459,c_2714,c_5224]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16364,plain,
% 3.73/0.99      ( r2_hidden(k1_xboole_0,k4_orders_2(sK5,sK6)) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_3156,c_16359]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_25,plain,
% 3.73/0.99      ( m2_orders_2(X0,X1,X2)
% 3.73/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.73/0.99      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_561,plain,
% 3.73/0.99      ( m2_orders_2(X0,X1,X2)
% 3.73/0.99      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 3.73/0.99      | sK6 != X2 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_562,plain,
% 3.73/0.99      ( m2_orders_2(X0,X1,sK6)
% 3.73/0.99      | ~ r2_hidden(X0,k4_orders_2(X1,sK6))
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_561]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_880,plain,
% 3.73/0.99      ( m2_orders_2(X0,X1,sK6)
% 3.73/0.99      | ~ r2_hidden(X0,k4_orders_2(X1,sK6))
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 3.73/0.99      | sK5 != X1 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_562,c_31]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_881,plain,
% 3.73/0.99      ( m2_orders_2(X0,sK5,sK6)
% 3.73/0.99      | ~ r2_hidden(X0,k4_orders_2(sK5,sK6))
% 3.73/0.99      | v2_struct_0(sK5)
% 3.73/0.99      | ~ v3_orders_2(sK5)
% 3.73/0.99      | ~ v4_orders_2(sK5)
% 3.73/0.99      | ~ v5_orders_2(sK5)
% 3.73/0.99      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_880]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_885,plain,
% 3.73/0.99      ( m2_orders_2(X0,sK5,sK6)
% 3.73/0.99      | ~ r2_hidden(X0,k4_orders_2(sK5,sK6))
% 3.73/0.99      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_881,c_35,c_34,c_33,c_32]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1010,plain,
% 3.73/0.99      ( m2_orders_2(X0,sK5,sK6) | ~ r2_hidden(X0,k4_orders_2(sK5,sK6)) ),
% 3.73/0.99      inference(equality_resolution_simp,[status(thm)],[c_885]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1011,plain,
% 3.73/0.99      ( m2_orders_2(X0,sK5,sK6) = iProver_top
% 3.73/0.99      | r2_hidden(X0,k4_orders_2(sK5,sK6)) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_1010]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1013,plain,
% 3.73/0.99      ( m2_orders_2(k1_xboole_0,sK5,sK6) = iProver_top
% 3.73/0.99      | r2_hidden(k1_xboole_0,k4_orders_2(sK5,sK6)) != iProver_top ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_28,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 3.73/0.99      | ~ m2_orders_2(X3,X1,X2)
% 3.73/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.73/0.99      | ~ r1_xboole_0(X3,X0)
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_528,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 3.73/0.99      | ~ m2_orders_2(X3,X1,X2)
% 3.73/0.99      | ~ r1_xboole_0(X3,X0)
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 3.73/0.99      | sK6 != X2 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_529,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,X1,sK6)
% 3.73/0.99      | ~ m2_orders_2(X2,X1,sK6)
% 3.73/0.99      | ~ r1_xboole_0(X0,X2)
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | ~ l1_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_528]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_901,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,X1,sK6)
% 3.73/0.99      | ~ m2_orders_2(X2,X1,sK6)
% 3.73/0.99      | ~ r1_xboole_0(X0,X2)
% 3.73/0.99      | v2_struct_0(X1)
% 3.73/0.99      | ~ v3_orders_2(X1)
% 3.73/0.99      | ~ v4_orders_2(X1)
% 3.73/0.99      | ~ v5_orders_2(X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 3.73/0.99      | sK5 != X1 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_529,c_31]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_902,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,sK5,sK6)
% 3.73/0.99      | ~ m2_orders_2(X1,sK5,sK6)
% 3.73/0.99      | ~ r1_xboole_0(X0,X1)
% 3.73/0.99      | v2_struct_0(sK5)
% 3.73/0.99      | ~ v3_orders_2(sK5)
% 3.73/0.99      | ~ v4_orders_2(sK5)
% 3.73/0.99      | ~ v5_orders_2(sK5)
% 3.73/0.99      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_901]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_906,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,sK5,sK6)
% 3.73/0.99      | ~ m2_orders_2(X1,sK5,sK6)
% 3.73/0.99      | ~ r1_xboole_0(X0,X1)
% 3.73/0.99      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_902,c_35,c_34,c_33,c_32]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1006,plain,
% 3.73/0.99      ( ~ m2_orders_2(X0,sK5,sK6)
% 3.73/0.99      | ~ m2_orders_2(X1,sK5,sK6)
% 3.73/0.99      | ~ r1_xboole_0(X0,X1) ),
% 3.73/0.99      inference(equality_resolution_simp,[status(thm)],[c_906]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1007,plain,
% 3.73/0.99      ( m2_orders_2(X0,sK5,sK6) != iProver_top
% 3.73/0.99      | m2_orders_2(X1,sK5,sK6) != iProver_top
% 3.73/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_1006]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1009,plain,
% 3.73/0.99      ( m2_orders_2(k1_xboole_0,sK5,sK6) != iProver_top
% 3.73/0.99      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_1007]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_9,plain,
% 3.73/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_94,plain,
% 3.73/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_96,plain,
% 3.73/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_94]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(contradiction,plain,
% 3.73/0.99      ( $false ),
% 3.73/0.99      inference(minisat,[status(thm)],[c_16364,c_1013,c_1009,c_96]) ).
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  ------                               Statistics
% 3.73/0.99  
% 3.73/0.99  ------ General
% 3.73/0.99  
% 3.73/0.99  abstr_ref_over_cycles:                  0
% 3.73/0.99  abstr_ref_under_cycles:                 0
% 3.73/0.99  gc_basic_clause_elim:                   0
% 3.73/0.99  forced_gc_time:                         0
% 3.73/0.99  parsing_time:                           0.019
% 3.73/0.99  unif_index_cands_time:                  0.
% 3.73/0.99  unif_index_add_time:                    0.
% 3.73/0.99  orderings_time:                         0.
% 3.73/0.99  out_proof_time:                         0.014
% 3.73/0.99  total_time:                             0.468
% 3.73/0.99  num_of_symbols:                         59
% 3.73/0.99  num_of_terms:                           17901
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing
% 3.73/0.99  
% 3.73/0.99  num_of_splits:                          0
% 3.73/0.99  num_of_split_atoms:                     0
% 3.73/0.99  num_of_reused_defs:                     0
% 3.73/0.99  num_eq_ax_congr_red:                    27
% 3.73/0.99  num_of_sem_filtered_clauses:            1
% 3.73/0.99  num_of_subtypes:                        0
% 3.73/0.99  monotx_restored_types:                  0
% 3.73/0.99  sat_num_of_epr_types:                   0
% 3.73/0.99  sat_num_of_non_cyclic_types:            0
% 3.73/0.99  sat_guarded_non_collapsed_types:        0
% 3.73/0.99  num_pure_diseq_elim:                    0
% 3.73/0.99  simp_replaced_by:                       0
% 3.73/0.99  res_preprocessed:                       154
% 3.73/0.99  prep_upred:                             0
% 3.73/0.99  prep_unflattend:                        17
% 3.73/0.99  smt_new_axioms:                         0
% 3.73/0.99  pred_elim_cands:                        5
% 3.73/0.99  pred_elim:                              7
% 3.73/0.99  pred_elim_cl:                           7
% 3.73/0.99  pred_elim_cycles:                       11
% 3.73/0.99  merged_defs:                            6
% 3.73/0.99  merged_defs_ncl:                        0
% 3.73/0.99  bin_hyper_res:                          6
% 3.73/0.99  prep_cycles:                            4
% 3.73/0.99  pred_elim_time:                         0.009
% 3.73/0.99  splitting_time:                         0.
% 3.73/0.99  sem_filter_time:                        0.
% 3.73/0.99  monotx_time:                            0.
% 3.73/0.99  subtype_inf_time:                       0.
% 3.73/0.99  
% 3.73/0.99  ------ Problem properties
% 3.73/0.99  
% 3.73/0.99  clauses:                                29
% 3.73/0.99  conjectures:                            1
% 3.73/0.99  epr:                                    5
% 3.73/0.99  horn:                                   23
% 3.73/0.99  ground:                                 3
% 3.73/0.99  unary:                                  12
% 3.73/0.99  binary:                                 8
% 3.73/0.99  lits:                                   56
% 3.73/0.99  lits_eq:                                9
% 3.73/0.99  fd_pure:                                0
% 3.73/0.99  fd_pseudo:                              0
% 3.73/0.99  fd_cond:                                2
% 3.73/0.99  fd_pseudo_cond:                         1
% 3.73/0.99  ac_symbols:                             0
% 3.73/0.99  
% 3.73/0.99  ------ Propositional Solver
% 3.73/0.99  
% 3.73/0.99  prop_solver_calls:                      29
% 3.73/0.99  prop_fast_solver_calls:                 1435
% 3.73/0.99  smt_solver_calls:                       0
% 3.73/0.99  smt_fast_solver_calls:                  0
% 3.73/0.99  prop_num_of_clauses:                    6534
% 3.73/0.99  prop_preprocess_simplified:             15817
% 3.73/0.99  prop_fo_subsumed:                       46
% 3.73/0.99  prop_solver_time:                       0.
% 3.73/0.99  smt_solver_time:                        0.
% 3.73/0.99  smt_fast_solver_time:                   0.
% 3.73/0.99  prop_fast_solver_time:                  0.
% 3.73/0.99  prop_unsat_core_time:                   0.
% 3.73/0.99  
% 3.73/0.99  ------ QBF
% 3.73/0.99  
% 3.73/0.99  qbf_q_res:                              0
% 3.73/0.99  qbf_num_tautologies:                    0
% 3.73/0.99  qbf_prep_cycles:                        0
% 3.73/0.99  
% 3.73/0.99  ------ BMC1
% 3.73/0.99  
% 3.73/0.99  bmc1_current_bound:                     -1
% 3.73/0.99  bmc1_last_solved_bound:                 -1
% 3.73/0.99  bmc1_unsat_core_size:                   -1
% 3.73/0.99  bmc1_unsat_core_parents_size:           -1
% 3.73/0.99  bmc1_merge_next_fun:                    0
% 3.73/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.73/0.99  
% 3.73/0.99  ------ Instantiation
% 3.73/0.99  
% 3.73/0.99  inst_num_of_clauses:                    1682
% 3.73/0.99  inst_num_in_passive:                    853
% 3.73/0.99  inst_num_in_active:                     676
% 3.73/0.99  inst_num_in_unprocessed:                153
% 3.73/0.99  inst_num_of_loops:                      760
% 3.73/0.99  inst_num_of_learning_restarts:          0
% 3.73/0.99  inst_num_moves_active_passive:          82
% 3.73/0.99  inst_lit_activity:                      0
% 3.73/0.99  inst_lit_activity_moves:                0
% 3.73/0.99  inst_num_tautologies:                   0
% 3.73/0.99  inst_num_prop_implied:                  0
% 3.73/0.99  inst_num_existing_simplified:           0
% 3.73/0.99  inst_num_eq_res_simplified:             0
% 3.73/0.99  inst_num_child_elim:                    0
% 3.73/0.99  inst_num_of_dismatching_blockings:      829
% 3.73/0.99  inst_num_of_non_proper_insts:           1829
% 3.73/0.99  inst_num_of_duplicates:                 0
% 3.73/0.99  inst_inst_num_from_inst_to_res:         0
% 3.73/0.99  inst_dismatching_checking_time:         0.
% 3.73/0.99  
% 3.73/0.99  ------ Resolution
% 3.73/0.99  
% 3.73/0.99  res_num_of_clauses:                     0
% 3.73/0.99  res_num_in_passive:                     0
% 3.73/0.99  res_num_in_active:                      0
% 3.73/0.99  res_num_of_loops:                       158
% 3.73/0.99  res_forward_subset_subsumed:            47
% 3.73/0.99  res_backward_subset_subsumed:           0
% 3.73/0.99  res_forward_subsumed:                   0
% 3.73/0.99  res_backward_subsumed:                  0
% 3.73/0.99  res_forward_subsumption_resolution:     0
% 3.73/0.99  res_backward_subsumption_resolution:    0
% 3.73/0.99  res_clause_to_clause_subsumption:       1614
% 3.73/0.99  res_orphan_elimination:                 0
% 3.73/0.99  res_tautology_del:                      82
% 3.73/0.99  res_num_eq_res_simplified:              7
% 3.73/0.99  res_num_sel_changes:                    0
% 3.73/0.99  res_moves_from_active_to_pass:          0
% 3.73/0.99  
% 3.73/0.99  ------ Superposition
% 3.73/0.99  
% 3.73/0.99  sup_time_total:                         0.
% 3.73/0.99  sup_time_generating:                    0.
% 3.73/0.99  sup_time_sim_full:                      0.
% 3.73/0.99  sup_time_sim_immed:                     0.
% 3.73/0.99  
% 3.73/0.99  sup_num_of_clauses:                     242
% 3.73/0.99  sup_num_in_active:                      150
% 3.73/0.99  sup_num_in_passive:                     92
% 3.73/0.99  sup_num_of_loops:                       151
% 3.73/0.99  sup_fw_superposition:                   235
% 3.73/0.99  sup_bw_superposition:                   105
% 3.73/0.99  sup_immediate_simplified:               74
% 3.73/0.99  sup_given_eliminated:                   0
% 3.73/0.99  comparisons_done:                       0
% 3.73/0.99  comparisons_avoided:                    0
% 3.73/0.99  
% 3.73/0.99  ------ Simplifications
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  sim_fw_subset_subsumed:                 46
% 3.73/0.99  sim_bw_subset_subsumed:                 6
% 3.73/0.99  sim_fw_subsumed:                        18
% 3.73/0.99  sim_bw_subsumed:                        0
% 3.73/0.99  sim_fw_subsumption_res:                 0
% 3.73/0.99  sim_bw_subsumption_res:                 0
% 3.73/0.99  sim_tautology_del:                      8
% 3.73/0.99  sim_eq_tautology_del:                   2
% 3.73/0.99  sim_eq_res_simp:                        0
% 3.73/0.99  sim_fw_demodulated:                     12
% 3.73/0.99  sim_bw_demodulated:                     0
% 3.73/0.99  sim_light_normalised:                   14
% 3.73/0.99  sim_joinable_taut:                      0
% 3.73/0.99  sim_joinable_simp:                      0
% 3.73/0.99  sim_ac_normalised:                      0
% 3.73/0.99  sim_smt_subsumption:                    0
% 3.73/0.99  
%------------------------------------------------------------------------------

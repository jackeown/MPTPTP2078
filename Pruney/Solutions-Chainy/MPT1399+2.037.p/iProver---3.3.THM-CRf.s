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
% DateTime   : Thu Dec  3 12:18:39 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 506 expanded)
%              Number of clauses        :   67 ( 135 expanded)
%              Number of leaves         :   17 ( 129 expanded)
%              Depth                    :   24
%              Number of atoms          :  446 (4752 expanded)
%              Number of equality atoms :   74 ( 419 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK4
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK4)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK4) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK3,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK3,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK2)
                      | ~ v3_pre_topc(X3,sK2) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK2)
                        & v3_pre_topc(X3,sK2) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k1_xboole_0 = sK4
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK4)
            | ~ r2_hidden(sK3,X3)
            | ~ v4_pre_topc(X3,sK2)
            | ~ v3_pre_topc(X3,sK2) )
          & ( ( r2_hidden(sK3,X3)
              & v4_pre_topc(X3,sK2)
              & v3_pre_topc(X3,sK2) )
            | ~ r2_hidden(X3,sK4) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).

fof(f63,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f40])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_181,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_182,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_345,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_346,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_45,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_348,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_22,c_21,c_45])).

cnf(c_433,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,X0)
    | k2_struct_0(sK2) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_348])).

cnf(c_434,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(k2_struct_0(sK2),sK4)
    | ~ r2_hidden(sK3,k2_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_13,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_42,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_436,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(k2_struct_0(sK2),sK4)
    | ~ r2_hidden(sK3,k2_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_22,c_21,c_42])).

cnf(c_605,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(k2_struct_0(sK2),sK4)
    | ~ r2_hidden(sK3,k2_struct_0(sK2))
    | k2_struct_0(sK2) != X0
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X1) ),
    inference(resolution_lifted,[status(thm)],[c_182,c_436])).

cnf(c_606,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),X0)
    | r2_hidden(k2_struct_0(sK2),sK4)
    | ~ r2_hidden(sK3,k2_struct_0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_1636,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),X0_47)
    | r2_hidden(k2_struct_0(sK2),sK4)
    | ~ r2_hidden(sK3,k2_struct_0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_606])).

cnf(c_1652,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),X0_47)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X0_47)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1636])).

cnf(c_2018,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X0_47)
    | r1_tarski(k2_struct_0(sK2),X0_47) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1652])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_320,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_9])).

cnf(c_360,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_21])).

cnf(c_361,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_1643,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_361])).

cnf(c_2085,plain,
    ( k1_zfmisc_1(k2_struct_0(sK2)) != k1_zfmisc_1(X0_47)
    | r1_tarski(k2_struct_0(sK2),X0_47) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2018,c_1643])).

cnf(c_2695,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2085])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_65,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1660,plain,
    ( X0_47 != X1_47
    | k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47) ),
    theory(equality)).

cnf(c_2362,plain,
    ( u1_struct_0(sK2) != X0_47
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_2585,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(k2_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_2657,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))
    | ~ sP0_iProver_split
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(k2_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_2658,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(k2_struct_0(sK2))
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2657])).

cnf(c_1653,plain,
    ( r2_hidden(k2_struct_0(sK2),sK4)
    | ~ r2_hidden(sK3,k2_struct_0(sK2))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1636])).

cnf(c_2017,plain,
    ( r2_hidden(k2_struct_0(sK2),sK4) = iProver_top
    | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1653])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1645,negated_conjecture,
    ( k1_xboole_0 = sK4 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2066,plain,
    ( r2_hidden(k2_struct_0(sK2),k1_xboole_0) = iProver_top
    | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2017,c_1645])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_552,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_553,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_48,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_51,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_555,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_23,c_21,c_48,c_51])).

cnf(c_1640,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_555])).

cnf(c_2013,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1640])).

cnf(c_2032,plain,
    ( r2_hidden(sK3,k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2013,c_1643])).

cnf(c_2070,plain,
    ( r2_hidden(k2_struct_0(sK2),k1_xboole_0) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2066,c_2032])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1650,plain,
    ( ~ r2_hidden(X0_47,X1_47)
    | ~ v1_xboole_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2005,plain,
    ( r2_hidden(X0_47,X1_47) != iProver_top
    | v1_xboole_0(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_2813,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_2005])).

cnf(c_3116,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2695,c_65,c_1643,c_2585,c_2658,c_2813])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1648,plain,
    ( r1_tarski(X0_47,X1_47)
    | r2_hidden(sK1(X0_47,X1_47),X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2007,plain,
    ( r1_tarski(X0_47,X1_47) = iProver_top
    | r2_hidden(sK1(X0_47,X1_47),X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1649,plain,
    ( r1_tarski(X0_47,X1_47)
    | ~ r2_hidden(sK1(X0_47,X1_47),X1_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2006,plain,
    ( r1_tarski(X0_47,X1_47) = iProver_top
    | r2_hidden(sK1(X0_47,X1_47),X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1649])).

cnf(c_2532,plain,
    ( r1_tarski(X0_47,X0_47) = iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_2006])).

cnf(c_3121,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3116,c_2532])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.40/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.40/0.99  
% 1.40/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.40/0.99  
% 1.40/0.99  ------  iProver source info
% 1.40/0.99  
% 1.40/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.40/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.40/0.99  git: non_committed_changes: false
% 1.40/0.99  git: last_make_outside_of_git: false
% 1.40/0.99  
% 1.40/0.99  ------ 
% 1.40/0.99  
% 1.40/0.99  ------ Input Options
% 1.40/0.99  
% 1.40/0.99  --out_options                           all
% 1.40/0.99  --tptp_safe_out                         true
% 1.40/0.99  --problem_path                          ""
% 1.40/0.99  --include_path                          ""
% 1.40/0.99  --clausifier                            res/vclausify_rel
% 1.40/0.99  --clausifier_options                    --mode clausify
% 1.40/0.99  --stdin                                 false
% 1.40/0.99  --stats_out                             all
% 1.40/0.99  
% 1.40/0.99  ------ General Options
% 1.40/0.99  
% 1.40/0.99  --fof                                   false
% 1.40/0.99  --time_out_real                         305.
% 1.40/0.99  --time_out_virtual                      -1.
% 1.40/0.99  --symbol_type_check                     false
% 1.40/0.99  --clausify_out                          false
% 1.40/0.99  --sig_cnt_out                           false
% 1.40/0.99  --trig_cnt_out                          false
% 1.40/0.99  --trig_cnt_out_tolerance                1.
% 1.40/0.99  --trig_cnt_out_sk_spl                   false
% 1.40/0.99  --abstr_cl_out                          false
% 1.40/0.99  
% 1.40/0.99  ------ Global Options
% 1.40/0.99  
% 1.40/0.99  --schedule                              default
% 1.40/0.99  --add_important_lit                     false
% 1.40/0.99  --prop_solver_per_cl                    1000
% 1.40/0.99  --min_unsat_core                        false
% 1.40/0.99  --soft_assumptions                      false
% 1.40/0.99  --soft_lemma_size                       3
% 1.40/0.99  --prop_impl_unit_size                   0
% 1.40/0.99  --prop_impl_unit                        []
% 1.40/0.99  --share_sel_clauses                     true
% 1.40/0.99  --reset_solvers                         false
% 1.40/0.99  --bc_imp_inh                            [conj_cone]
% 1.40/0.99  --conj_cone_tolerance                   3.
% 1.40/0.99  --extra_neg_conj                        none
% 1.40/0.99  --large_theory_mode                     true
% 1.40/0.99  --prolific_symb_bound                   200
% 1.40/0.99  --lt_threshold                          2000
% 1.40/0.99  --clause_weak_htbl                      true
% 1.40/0.99  --gc_record_bc_elim                     false
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing Options
% 1.40/0.99  
% 1.40/0.99  --preprocessing_flag                    true
% 1.40/0.99  --time_out_prep_mult                    0.1
% 1.40/0.99  --splitting_mode                        input
% 1.40/0.99  --splitting_grd                         true
% 1.40/0.99  --splitting_cvd                         false
% 1.40/0.99  --splitting_cvd_svl                     false
% 1.40/0.99  --splitting_nvd                         32
% 1.40/0.99  --sub_typing                            true
% 1.40/0.99  --prep_gs_sim                           true
% 1.40/0.99  --prep_unflatten                        true
% 1.40/0.99  --prep_res_sim                          true
% 1.40/0.99  --prep_upred                            true
% 1.40/0.99  --prep_sem_filter                       exhaustive
% 1.40/0.99  --prep_sem_filter_out                   false
% 1.40/0.99  --pred_elim                             true
% 1.40/0.99  --res_sim_input                         true
% 1.40/0.99  --eq_ax_congr_red                       true
% 1.40/0.99  --pure_diseq_elim                       true
% 1.40/0.99  --brand_transform                       false
% 1.40/0.99  --non_eq_to_eq                          false
% 1.40/0.99  --prep_def_merge                        true
% 1.40/0.99  --prep_def_merge_prop_impl              false
% 1.40/0.99  --prep_def_merge_mbd                    true
% 1.40/0.99  --prep_def_merge_tr_red                 false
% 1.40/0.99  --prep_def_merge_tr_cl                  false
% 1.40/0.99  --smt_preprocessing                     true
% 1.40/0.99  --smt_ac_axioms                         fast
% 1.40/0.99  --preprocessed_out                      false
% 1.40/0.99  --preprocessed_stats                    false
% 1.40/0.99  
% 1.40/0.99  ------ Abstraction refinement Options
% 1.40/0.99  
% 1.40/0.99  --abstr_ref                             []
% 1.40/0.99  --abstr_ref_prep                        false
% 1.40/0.99  --abstr_ref_until_sat                   false
% 1.40/0.99  --abstr_ref_sig_restrict                funpre
% 1.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.40/0.99  --abstr_ref_under                       []
% 1.40/0.99  
% 1.40/0.99  ------ SAT Options
% 1.40/0.99  
% 1.40/0.99  --sat_mode                              false
% 1.40/0.99  --sat_fm_restart_options                ""
% 1.40/0.99  --sat_gr_def                            false
% 1.40/0.99  --sat_epr_types                         true
% 1.40/0.99  --sat_non_cyclic_types                  false
% 1.40/0.99  --sat_finite_models                     false
% 1.40/0.99  --sat_fm_lemmas                         false
% 1.40/0.99  --sat_fm_prep                           false
% 1.40/0.99  --sat_fm_uc_incr                        true
% 1.40/0.99  --sat_out_model                         small
% 1.40/0.99  --sat_out_clauses                       false
% 1.40/0.99  
% 1.40/0.99  ------ QBF Options
% 1.40/0.99  
% 1.40/0.99  --qbf_mode                              false
% 1.40/0.99  --qbf_elim_univ                         false
% 1.40/0.99  --qbf_dom_inst                          none
% 1.40/0.99  --qbf_dom_pre_inst                      false
% 1.40/0.99  --qbf_sk_in                             false
% 1.40/0.99  --qbf_pred_elim                         true
% 1.40/0.99  --qbf_split                             512
% 1.40/0.99  
% 1.40/0.99  ------ BMC1 Options
% 1.40/0.99  
% 1.40/0.99  --bmc1_incremental                      false
% 1.40/0.99  --bmc1_axioms                           reachable_all
% 1.40/0.99  --bmc1_min_bound                        0
% 1.40/0.99  --bmc1_max_bound                        -1
% 1.40/0.99  --bmc1_max_bound_default                -1
% 1.40/0.99  --bmc1_symbol_reachability              true
% 1.40/0.99  --bmc1_property_lemmas                  false
% 1.40/0.99  --bmc1_k_induction                      false
% 1.40/0.99  --bmc1_non_equiv_states                 false
% 1.40/0.99  --bmc1_deadlock                         false
% 1.40/0.99  --bmc1_ucm                              false
% 1.40/0.99  --bmc1_add_unsat_core                   none
% 1.40/0.99  --bmc1_unsat_core_children              false
% 1.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.40/0.99  --bmc1_out_stat                         full
% 1.40/0.99  --bmc1_ground_init                      false
% 1.40/0.99  --bmc1_pre_inst_next_state              false
% 1.40/0.99  --bmc1_pre_inst_state                   false
% 1.40/0.99  --bmc1_pre_inst_reach_state             false
% 1.40/0.99  --bmc1_out_unsat_core                   false
% 1.40/0.99  --bmc1_aig_witness_out                  false
% 1.40/0.99  --bmc1_verbose                          false
% 1.40/0.99  --bmc1_dump_clauses_tptp                false
% 1.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.40/0.99  --bmc1_dump_file                        -
% 1.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.40/0.99  --bmc1_ucm_extend_mode                  1
% 1.40/0.99  --bmc1_ucm_init_mode                    2
% 1.40/0.99  --bmc1_ucm_cone_mode                    none
% 1.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.40/0.99  --bmc1_ucm_relax_model                  4
% 1.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.40/0.99  --bmc1_ucm_layered_model                none
% 1.40/0.99  --bmc1_ucm_max_lemma_size               10
% 1.40/0.99  
% 1.40/0.99  ------ AIG Options
% 1.40/0.99  
% 1.40/0.99  --aig_mode                              false
% 1.40/0.99  
% 1.40/0.99  ------ Instantiation Options
% 1.40/0.99  
% 1.40/0.99  --instantiation_flag                    true
% 1.40/0.99  --inst_sos_flag                         false
% 1.40/0.99  --inst_sos_phase                        true
% 1.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.40/0.99  --inst_lit_sel_side                     num_symb
% 1.40/0.99  --inst_solver_per_active                1400
% 1.40/0.99  --inst_solver_calls_frac                1.
% 1.40/0.99  --inst_passive_queue_type               priority_queues
% 1.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.40/0.99  --inst_passive_queues_freq              [25;2]
% 1.40/0.99  --inst_dismatching                      true
% 1.40/0.99  --inst_eager_unprocessed_to_passive     true
% 1.40/0.99  --inst_prop_sim_given                   true
% 1.40/0.99  --inst_prop_sim_new                     false
% 1.40/0.99  --inst_subs_new                         false
% 1.40/0.99  --inst_eq_res_simp                      false
% 1.40/0.99  --inst_subs_given                       false
% 1.40/0.99  --inst_orphan_elimination               true
% 1.40/0.99  --inst_learning_loop_flag               true
% 1.40/0.99  --inst_learning_start                   3000
% 1.40/0.99  --inst_learning_factor                  2
% 1.40/0.99  --inst_start_prop_sim_after_learn       3
% 1.40/0.99  --inst_sel_renew                        solver
% 1.40/0.99  --inst_lit_activity_flag                true
% 1.40/0.99  --inst_restr_to_given                   false
% 1.40/0.99  --inst_activity_threshold               500
% 1.40/0.99  --inst_out_proof                        true
% 1.40/0.99  
% 1.40/0.99  ------ Resolution Options
% 1.40/0.99  
% 1.40/0.99  --resolution_flag                       true
% 1.40/0.99  --res_lit_sel                           adaptive
% 1.40/0.99  --res_lit_sel_side                      none
% 1.40/0.99  --res_ordering                          kbo
% 1.40/0.99  --res_to_prop_solver                    active
% 1.40/0.99  --res_prop_simpl_new                    false
% 1.40/0.99  --res_prop_simpl_given                  true
% 1.40/0.99  --res_passive_queue_type                priority_queues
% 1.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/0.99  --res_passive_queues_freq               [15;5]
% 1.40/0.99  --res_forward_subs                      full
% 1.40/0.99  --res_backward_subs                     full
% 1.40/0.99  --res_forward_subs_resolution           true
% 1.40/0.99  --res_backward_subs_resolution          true
% 1.40/0.99  --res_orphan_elimination                true
% 1.40/0.99  --res_time_limit                        2.
% 1.40/0.99  --res_out_proof                         true
% 1.40/0.99  
% 1.40/0.99  ------ Superposition Options
% 1.40/0.99  
% 1.40/0.99  --superposition_flag                    true
% 1.40/0.99  --sup_passive_queue_type                priority_queues
% 1.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.40/0.99  --demod_completeness_check              fast
% 1.40/0.99  --demod_use_ground                      true
% 1.40/0.99  --sup_to_prop_solver                    passive
% 1.40/0.99  --sup_prop_simpl_new                    true
% 1.40/0.99  --sup_prop_simpl_given                  true
% 1.40/0.99  --sup_fun_splitting                     false
% 1.40/0.99  --sup_smt_interval                      50000
% 1.40/0.99  
% 1.40/0.99  ------ Superposition Simplification Setup
% 1.40/0.99  
% 1.40/0.99  --sup_indices_passive                   []
% 1.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_full_bw                           [BwDemod]
% 1.40/0.99  --sup_immed_triv                        [TrivRules]
% 1.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_immed_bw_main                     []
% 1.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.99  
% 1.40/0.99  ------ Combination Options
% 1.40/0.99  
% 1.40/0.99  --comb_res_mult                         3
% 1.40/0.99  --comb_sup_mult                         2
% 1.40/0.99  --comb_inst_mult                        10
% 1.40/0.99  
% 1.40/0.99  ------ Debug Options
% 1.40/0.99  
% 1.40/0.99  --dbg_backtrace                         false
% 1.40/0.99  --dbg_dump_prop_clauses                 false
% 1.40/0.99  --dbg_dump_prop_clauses_file            -
% 1.40/0.99  --dbg_out_stat                          false
% 1.40/0.99  ------ Parsing...
% 1.40/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.40/0.99  ------ Proving...
% 1.40/0.99  ------ Problem Properties 
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  clauses                                 21
% 1.40/0.99  conjectures                             1
% 1.40/0.99  EPR                                     4
% 1.40/0.99  Horn                                    16
% 1.40/0.99  unary                                   5
% 1.40/0.99  binary                                  7
% 1.40/0.99  lits                                    49
% 1.40/0.99  lits eq                                 12
% 1.40/0.99  fd_pure                                 0
% 1.40/0.99  fd_pseudo                               0
% 1.40/0.99  fd_cond                                 0
% 1.40/0.99  fd_pseudo_cond                          0
% 1.40/0.99  AC symbols                              0
% 1.40/0.99  
% 1.40/0.99  ------ Schedule dynamic 5 is on 
% 1.40/0.99  
% 1.40/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  ------ 
% 1.40/0.99  Current options:
% 1.40/0.99  ------ 
% 1.40/0.99  
% 1.40/0.99  ------ Input Options
% 1.40/0.99  
% 1.40/0.99  --out_options                           all
% 1.40/0.99  --tptp_safe_out                         true
% 1.40/0.99  --problem_path                          ""
% 1.40/0.99  --include_path                          ""
% 1.40/0.99  --clausifier                            res/vclausify_rel
% 1.40/0.99  --clausifier_options                    --mode clausify
% 1.40/0.99  --stdin                                 false
% 1.40/0.99  --stats_out                             all
% 1.40/0.99  
% 1.40/0.99  ------ General Options
% 1.40/0.99  
% 1.40/0.99  --fof                                   false
% 1.40/0.99  --time_out_real                         305.
% 1.40/0.99  --time_out_virtual                      -1.
% 1.40/0.99  --symbol_type_check                     false
% 1.40/0.99  --clausify_out                          false
% 1.40/0.99  --sig_cnt_out                           false
% 1.40/0.99  --trig_cnt_out                          false
% 1.40/0.99  --trig_cnt_out_tolerance                1.
% 1.40/0.99  --trig_cnt_out_sk_spl                   false
% 1.40/0.99  --abstr_cl_out                          false
% 1.40/0.99  
% 1.40/0.99  ------ Global Options
% 1.40/0.99  
% 1.40/0.99  --schedule                              default
% 1.40/0.99  --add_important_lit                     false
% 1.40/0.99  --prop_solver_per_cl                    1000
% 1.40/0.99  --min_unsat_core                        false
% 1.40/0.99  --soft_assumptions                      false
% 1.40/0.99  --soft_lemma_size                       3
% 1.40/0.99  --prop_impl_unit_size                   0
% 1.40/0.99  --prop_impl_unit                        []
% 1.40/0.99  --share_sel_clauses                     true
% 1.40/0.99  --reset_solvers                         false
% 1.40/0.99  --bc_imp_inh                            [conj_cone]
% 1.40/0.99  --conj_cone_tolerance                   3.
% 1.40/0.99  --extra_neg_conj                        none
% 1.40/0.99  --large_theory_mode                     true
% 1.40/0.99  --prolific_symb_bound                   200
% 1.40/0.99  --lt_threshold                          2000
% 1.40/0.99  --clause_weak_htbl                      true
% 1.40/0.99  --gc_record_bc_elim                     false
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing Options
% 1.40/0.99  
% 1.40/0.99  --preprocessing_flag                    true
% 1.40/0.99  --time_out_prep_mult                    0.1
% 1.40/0.99  --splitting_mode                        input
% 1.40/0.99  --splitting_grd                         true
% 1.40/0.99  --splitting_cvd                         false
% 1.40/0.99  --splitting_cvd_svl                     false
% 1.40/0.99  --splitting_nvd                         32
% 1.40/0.99  --sub_typing                            true
% 1.40/0.99  --prep_gs_sim                           true
% 1.40/0.99  --prep_unflatten                        true
% 1.40/0.99  --prep_res_sim                          true
% 1.40/0.99  --prep_upred                            true
% 1.40/0.99  --prep_sem_filter                       exhaustive
% 1.40/0.99  --prep_sem_filter_out                   false
% 1.40/0.99  --pred_elim                             true
% 1.40/0.99  --res_sim_input                         true
% 1.40/0.99  --eq_ax_congr_red                       true
% 1.40/0.99  --pure_diseq_elim                       true
% 1.40/0.99  --brand_transform                       false
% 1.40/0.99  --non_eq_to_eq                          false
% 1.40/0.99  --prep_def_merge                        true
% 1.40/0.99  --prep_def_merge_prop_impl              false
% 1.40/0.99  --prep_def_merge_mbd                    true
% 1.40/0.99  --prep_def_merge_tr_red                 false
% 1.40/0.99  --prep_def_merge_tr_cl                  false
% 1.40/0.99  --smt_preprocessing                     true
% 1.40/0.99  --smt_ac_axioms                         fast
% 1.40/0.99  --preprocessed_out                      false
% 1.40/0.99  --preprocessed_stats                    false
% 1.40/0.99  
% 1.40/0.99  ------ Abstraction refinement Options
% 1.40/0.99  
% 1.40/0.99  --abstr_ref                             []
% 1.40/0.99  --abstr_ref_prep                        false
% 1.40/0.99  --abstr_ref_until_sat                   false
% 1.40/0.99  --abstr_ref_sig_restrict                funpre
% 1.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.40/0.99  --abstr_ref_under                       []
% 1.40/0.99  
% 1.40/0.99  ------ SAT Options
% 1.40/0.99  
% 1.40/0.99  --sat_mode                              false
% 1.40/0.99  --sat_fm_restart_options                ""
% 1.40/0.99  --sat_gr_def                            false
% 1.40/0.99  --sat_epr_types                         true
% 1.40/0.99  --sat_non_cyclic_types                  false
% 1.40/0.99  --sat_finite_models                     false
% 1.40/0.99  --sat_fm_lemmas                         false
% 1.40/0.99  --sat_fm_prep                           false
% 1.40/0.99  --sat_fm_uc_incr                        true
% 1.40/0.99  --sat_out_model                         small
% 1.40/0.99  --sat_out_clauses                       false
% 1.40/0.99  
% 1.40/0.99  ------ QBF Options
% 1.40/0.99  
% 1.40/0.99  --qbf_mode                              false
% 1.40/0.99  --qbf_elim_univ                         false
% 1.40/0.99  --qbf_dom_inst                          none
% 1.40/0.99  --qbf_dom_pre_inst                      false
% 1.40/0.99  --qbf_sk_in                             false
% 1.40/0.99  --qbf_pred_elim                         true
% 1.40/0.99  --qbf_split                             512
% 1.40/0.99  
% 1.40/0.99  ------ BMC1 Options
% 1.40/0.99  
% 1.40/0.99  --bmc1_incremental                      false
% 1.40/0.99  --bmc1_axioms                           reachable_all
% 1.40/0.99  --bmc1_min_bound                        0
% 1.40/0.99  --bmc1_max_bound                        -1
% 1.40/0.99  --bmc1_max_bound_default                -1
% 1.40/0.99  --bmc1_symbol_reachability              true
% 1.40/0.99  --bmc1_property_lemmas                  false
% 1.40/0.99  --bmc1_k_induction                      false
% 1.40/0.99  --bmc1_non_equiv_states                 false
% 1.40/0.99  --bmc1_deadlock                         false
% 1.40/0.99  --bmc1_ucm                              false
% 1.40/0.99  --bmc1_add_unsat_core                   none
% 1.40/0.99  --bmc1_unsat_core_children              false
% 1.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.40/0.99  --bmc1_out_stat                         full
% 1.40/0.99  --bmc1_ground_init                      false
% 1.40/0.99  --bmc1_pre_inst_next_state              false
% 1.40/0.99  --bmc1_pre_inst_state                   false
% 1.40/0.99  --bmc1_pre_inst_reach_state             false
% 1.40/0.99  --bmc1_out_unsat_core                   false
% 1.40/0.99  --bmc1_aig_witness_out                  false
% 1.40/0.99  --bmc1_verbose                          false
% 1.40/0.99  --bmc1_dump_clauses_tptp                false
% 1.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.40/0.99  --bmc1_dump_file                        -
% 1.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.40/0.99  --bmc1_ucm_extend_mode                  1
% 1.40/0.99  --bmc1_ucm_init_mode                    2
% 1.40/0.99  --bmc1_ucm_cone_mode                    none
% 1.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.40/0.99  --bmc1_ucm_relax_model                  4
% 1.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.40/0.99  --bmc1_ucm_layered_model                none
% 1.40/0.99  --bmc1_ucm_max_lemma_size               10
% 1.40/0.99  
% 1.40/0.99  ------ AIG Options
% 1.40/0.99  
% 1.40/0.99  --aig_mode                              false
% 1.40/0.99  
% 1.40/0.99  ------ Instantiation Options
% 1.40/0.99  
% 1.40/0.99  --instantiation_flag                    true
% 1.40/0.99  --inst_sos_flag                         false
% 1.40/0.99  --inst_sos_phase                        true
% 1.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.40/0.99  --inst_lit_sel_side                     none
% 1.40/0.99  --inst_solver_per_active                1400
% 1.40/0.99  --inst_solver_calls_frac                1.
% 1.40/0.99  --inst_passive_queue_type               priority_queues
% 1.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.40/0.99  --inst_passive_queues_freq              [25;2]
% 1.40/0.99  --inst_dismatching                      true
% 1.40/0.99  --inst_eager_unprocessed_to_passive     true
% 1.40/0.99  --inst_prop_sim_given                   true
% 1.40/0.99  --inst_prop_sim_new                     false
% 1.40/0.99  --inst_subs_new                         false
% 1.40/0.99  --inst_eq_res_simp                      false
% 1.40/0.99  --inst_subs_given                       false
% 1.40/0.99  --inst_orphan_elimination               true
% 1.40/0.99  --inst_learning_loop_flag               true
% 1.40/0.99  --inst_learning_start                   3000
% 1.40/0.99  --inst_learning_factor                  2
% 1.40/0.99  --inst_start_prop_sim_after_learn       3
% 1.40/0.99  --inst_sel_renew                        solver
% 1.40/0.99  --inst_lit_activity_flag                true
% 1.40/0.99  --inst_restr_to_given                   false
% 1.40/0.99  --inst_activity_threshold               500
% 1.40/0.99  --inst_out_proof                        true
% 1.40/0.99  
% 1.40/0.99  ------ Resolution Options
% 1.40/0.99  
% 1.40/0.99  --resolution_flag                       false
% 1.40/0.99  --res_lit_sel                           adaptive
% 1.40/0.99  --res_lit_sel_side                      none
% 1.40/0.99  --res_ordering                          kbo
% 1.40/0.99  --res_to_prop_solver                    active
% 1.40/0.99  --res_prop_simpl_new                    false
% 1.40/0.99  --res_prop_simpl_given                  true
% 1.40/0.99  --res_passive_queue_type                priority_queues
% 1.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/0.99  --res_passive_queues_freq               [15;5]
% 1.40/0.99  --res_forward_subs                      full
% 1.40/0.99  --res_backward_subs                     full
% 1.40/0.99  --res_forward_subs_resolution           true
% 1.40/0.99  --res_backward_subs_resolution          true
% 1.40/0.99  --res_orphan_elimination                true
% 1.40/0.99  --res_time_limit                        2.
% 1.40/0.99  --res_out_proof                         true
% 1.40/0.99  
% 1.40/0.99  ------ Superposition Options
% 1.40/0.99  
% 1.40/0.99  --superposition_flag                    true
% 1.40/0.99  --sup_passive_queue_type                priority_queues
% 1.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.40/0.99  --demod_completeness_check              fast
% 1.40/0.99  --demod_use_ground                      true
% 1.40/0.99  --sup_to_prop_solver                    passive
% 1.40/0.99  --sup_prop_simpl_new                    true
% 1.40/0.99  --sup_prop_simpl_given                  true
% 1.40/0.99  --sup_fun_splitting                     false
% 1.40/0.99  --sup_smt_interval                      50000
% 1.40/0.99  
% 1.40/0.99  ------ Superposition Simplification Setup
% 1.40/0.99  
% 1.40/0.99  --sup_indices_passive                   []
% 1.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_full_bw                           [BwDemod]
% 1.40/0.99  --sup_immed_triv                        [TrivRules]
% 1.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_immed_bw_main                     []
% 1.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.99  
% 1.40/0.99  ------ Combination Options
% 1.40/0.99  
% 1.40/0.99  --comb_res_mult                         3
% 1.40/0.99  --comb_sup_mult                         2
% 1.40/0.99  --comb_inst_mult                        10
% 1.40/0.99  
% 1.40/0.99  ------ Debug Options
% 1.40/0.99  
% 1.40/0.99  --dbg_backtrace                         false
% 1.40/0.99  --dbg_dump_prop_clauses                 false
% 1.40/0.99  --dbg_dump_prop_clauses_file            -
% 1.40/0.99  --dbg_out_stat                          false
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  ------ Proving...
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  % SZS status Theorem for theBenchmark.p
% 1.40/0.99  
% 1.40/0.99   Resolution empty clause
% 1.40/0.99  
% 1.40/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.40/0.99  
% 1.40/0.99  fof(f5,axiom,(
% 1.40/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f34,plain,(
% 1.40/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.40/0.99    inference(nnf_transformation,[],[f5])).
% 1.40/0.99  
% 1.40/0.99  fof(f49,plain,(
% 1.40/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f34])).
% 1.40/0.99  
% 1.40/0.99  fof(f11,conjecture,(
% 1.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f12,negated_conjecture,(
% 1.40/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.40/0.99    inference(negated_conjecture,[],[f11])).
% 1.40/0.99  
% 1.40/0.99  fof(f24,plain,(
% 1.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.40/0.99    inference(ennf_transformation,[],[f12])).
% 1.40/0.99  
% 1.40/0.99  fof(f25,plain,(
% 1.40/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.40/0.99    inference(flattening,[],[f24])).
% 1.40/0.99  
% 1.40/0.99  fof(f35,plain,(
% 1.40/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.40/0.99    inference(nnf_transformation,[],[f25])).
% 1.40/0.99  
% 1.40/0.99  fof(f36,plain,(
% 1.40/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.40/0.99    inference(flattening,[],[f35])).
% 1.40/0.99  
% 1.40/0.99  fof(f39,plain,(
% 1.40/0.99    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.40/0.99    introduced(choice_axiom,[])).
% 1.40/0.99  
% 1.40/0.99  fof(f38,plain,(
% 1.40/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.40/0.99    introduced(choice_axiom,[])).
% 1.40/0.99  
% 1.40/0.99  fof(f37,plain,(
% 1.40/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.40/0.99    introduced(choice_axiom,[])).
% 1.40/0.99  
% 1.40/0.99  fof(f40,plain,(
% 1.40/0.99    ((k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).
% 1.40/0.99  
% 1.40/0.99  fof(f63,plain,(
% 1.40/0.99    ( ! [X3] : (r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.40/0.99    inference(cnf_transformation,[],[f40])).
% 1.40/0.99  
% 1.40/0.99  fof(f9,axiom,(
% 1.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f20,plain,(
% 1.40/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.40/0.99    inference(ennf_transformation,[],[f9])).
% 1.40/0.99  
% 1.40/0.99  fof(f21,plain,(
% 1.40/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.40/0.99    inference(flattening,[],[f20])).
% 1.40/0.99  
% 1.40/0.99  fof(f53,plain,(
% 1.40/0.99    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f21])).
% 1.40/0.99  
% 1.40/0.99  fof(f56,plain,(
% 1.40/0.99    v2_pre_topc(sK2)),
% 1.40/0.99    inference(cnf_transformation,[],[f40])).
% 1.40/0.99  
% 1.40/0.99  fof(f57,plain,(
% 1.40/0.99    l1_pre_topc(sK2)),
% 1.40/0.99    inference(cnf_transformation,[],[f40])).
% 1.40/0.99  
% 1.40/0.99  fof(f10,axiom,(
% 1.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f22,plain,(
% 1.40/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.40/0.99    inference(ennf_transformation,[],[f10])).
% 1.40/0.99  
% 1.40/0.99  fof(f23,plain,(
% 1.40/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.40/0.99    inference(flattening,[],[f22])).
% 1.40/0.99  
% 1.40/0.99  fof(f54,plain,(
% 1.40/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f23])).
% 1.40/0.99  
% 1.40/0.99  fof(f7,axiom,(
% 1.40/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f17,plain,(
% 1.40/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.40/0.99    inference(ennf_transformation,[],[f7])).
% 1.40/0.99  
% 1.40/0.99  fof(f51,plain,(
% 1.40/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f17])).
% 1.40/0.99  
% 1.40/0.99  fof(f6,axiom,(
% 1.40/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f16,plain,(
% 1.40/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.40/0.99    inference(ennf_transformation,[],[f6])).
% 1.40/0.99  
% 1.40/0.99  fof(f50,plain,(
% 1.40/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f16])).
% 1.40/0.99  
% 1.40/0.99  fof(f3,axiom,(
% 1.40/0.99    v1_xboole_0(k1_xboole_0)),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f46,plain,(
% 1.40/0.99    v1_xboole_0(k1_xboole_0)),
% 1.40/0.99    inference(cnf_transformation,[],[f3])).
% 1.40/0.99  
% 1.40/0.99  fof(f64,plain,(
% 1.40/0.99    k1_xboole_0 = sK4),
% 1.40/0.99    inference(cnf_transformation,[],[f40])).
% 1.40/0.99  
% 1.40/0.99  fof(f4,axiom,(
% 1.40/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f14,plain,(
% 1.40/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.40/0.99    inference(ennf_transformation,[],[f4])).
% 1.40/0.99  
% 1.40/0.99  fof(f15,plain,(
% 1.40/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.40/0.99    inference(flattening,[],[f14])).
% 1.40/0.99  
% 1.40/0.99  fof(f47,plain,(
% 1.40/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f15])).
% 1.40/0.99  
% 1.40/0.99  fof(f58,plain,(
% 1.40/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.40/0.99    inference(cnf_transformation,[],[f40])).
% 1.40/0.99  
% 1.40/0.99  fof(f55,plain,(
% 1.40/0.99    ~v2_struct_0(sK2)),
% 1.40/0.99    inference(cnf_transformation,[],[f40])).
% 1.40/0.99  
% 1.40/0.99  fof(f8,axiom,(
% 1.40/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f18,plain,(
% 1.40/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.40/0.99    inference(ennf_transformation,[],[f8])).
% 1.40/0.99  
% 1.40/0.99  fof(f19,plain,(
% 1.40/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/0.99    inference(flattening,[],[f18])).
% 1.40/0.99  
% 1.40/0.99  fof(f52,plain,(
% 1.40/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f19])).
% 1.40/0.99  
% 1.40/0.99  fof(f1,axiom,(
% 1.40/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f26,plain,(
% 1.40/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.99    inference(nnf_transformation,[],[f1])).
% 1.40/0.99  
% 1.40/0.99  fof(f27,plain,(
% 1.40/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.99    inference(rectify,[],[f26])).
% 1.40/0.99  
% 1.40/0.99  fof(f28,plain,(
% 1.40/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.40/0.99    introduced(choice_axiom,[])).
% 1.40/0.99  
% 1.40/0.99  fof(f29,plain,(
% 1.40/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 1.40/0.99  
% 1.40/0.99  fof(f41,plain,(
% 1.40/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f29])).
% 1.40/0.99  
% 1.40/0.99  fof(f2,axiom,(
% 1.40/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f13,plain,(
% 1.40/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.99    inference(ennf_transformation,[],[f2])).
% 1.40/0.99  
% 1.40/0.99  fof(f30,plain,(
% 1.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.99    inference(nnf_transformation,[],[f13])).
% 1.40/0.99  
% 1.40/0.99  fof(f31,plain,(
% 1.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.99    inference(rectify,[],[f30])).
% 1.40/0.99  
% 1.40/0.99  fof(f32,plain,(
% 1.40/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.40/0.99    introduced(choice_axiom,[])).
% 1.40/0.99  
% 1.40/0.99  fof(f33,plain,(
% 1.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 1.40/0.99  
% 1.40/0.99  fof(f44,plain,(
% 1.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f33])).
% 1.40/0.99  
% 1.40/0.99  fof(f45,plain,(
% 1.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f33])).
% 1.40/0.99  
% 1.40/0.99  cnf(c_7,plain,
% 1.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.40/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_181,plain,
% 1.40/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.40/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_182,plain,
% 1.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.40/0.99      inference(renaming,[status(thm)],[c_181]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_15,negated_conjecture,
% 1.40/0.99      ( ~ v3_pre_topc(X0,sK2)
% 1.40/0.99      | ~ v4_pre_topc(X0,sK2)
% 1.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.40/0.99      | r2_hidden(X0,sK4)
% 1.40/0.99      | ~ r2_hidden(sK3,X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_12,plain,
% 1.40/0.99      ( v4_pre_topc(k2_struct_0(X0),X0)
% 1.40/0.99      | ~ v2_pre_topc(X0)
% 1.40/0.99      | ~ l1_pre_topc(X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_22,negated_conjecture,
% 1.40/0.99      ( v2_pre_topc(sK2) ),
% 1.40/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_345,plain,
% 1.40/0.99      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK2 != X0 ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_346,plain,
% 1.40/0.99      ( v4_pre_topc(k2_struct_0(sK2),sK2) | ~ l1_pre_topc(sK2) ),
% 1.40/0.99      inference(unflattening,[status(thm)],[c_345]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_21,negated_conjecture,
% 1.40/0.99      ( l1_pre_topc(sK2) ),
% 1.40/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_45,plain,
% 1.40/0.99      ( v4_pre_topc(k2_struct_0(sK2),sK2)
% 1.40/0.99      | ~ v2_pre_topc(sK2)
% 1.40/0.99      | ~ l1_pre_topc(sK2) ),
% 1.40/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_348,plain,
% 1.40/0.99      ( v4_pre_topc(k2_struct_0(sK2),sK2) ),
% 1.40/0.99      inference(global_propositional_subsumption,
% 1.40/0.99                [status(thm)],
% 1.40/0.99                [c_346,c_22,c_21,c_45]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_433,plain,
% 1.40/0.99      ( ~ v3_pre_topc(X0,sK2)
% 1.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.40/0.99      | r2_hidden(X0,sK4)
% 1.40/0.99      | ~ r2_hidden(sK3,X0)
% 1.40/0.99      | k2_struct_0(sK2) != X0
% 1.40/0.99      | sK2 != sK2 ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_348]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_434,plain,
% 1.40/0.99      ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
% 1.40/0.99      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.40/0.99      | r2_hidden(k2_struct_0(sK2),sK4)
% 1.40/0.99      | ~ r2_hidden(sK3,k2_struct_0(sK2)) ),
% 1.40/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_13,plain,
% 1.40/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 1.40/0.99      | ~ v2_pre_topc(X0)
% 1.40/0.99      | ~ l1_pre_topc(X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_42,plain,
% 1.40/0.99      ( v3_pre_topc(k2_struct_0(sK2),sK2)
% 1.40/0.99      | ~ v2_pre_topc(sK2)
% 1.40/0.99      | ~ l1_pre_topc(sK2) ),
% 1.40/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_436,plain,
% 1.40/0.99      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.40/0.99      | r2_hidden(k2_struct_0(sK2),sK4)
% 1.40/0.99      | ~ r2_hidden(sK3,k2_struct_0(sK2)) ),
% 1.40/0.99      inference(global_propositional_subsumption,
% 1.40/0.99                [status(thm)],
% 1.40/0.99                [c_434,c_22,c_21,c_42]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_605,plain,
% 1.40/0.99      ( ~ r1_tarski(X0,X1)
% 1.40/0.99      | r2_hidden(k2_struct_0(sK2),sK4)
% 1.40/0.99      | ~ r2_hidden(sK3,k2_struct_0(sK2))
% 1.40/0.99      | k2_struct_0(sK2) != X0
% 1.40/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X1) ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_182,c_436]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_606,plain,
% 1.40/1.00      ( ~ r1_tarski(k2_struct_0(sK2),X0)
% 1.40/1.00      | r2_hidden(k2_struct_0(sK2),sK4)
% 1.40/1.00      | ~ r2_hidden(sK3,k2_struct_0(sK2))
% 1.40/1.00      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X0) ),
% 1.40/1.00      inference(unflattening,[status(thm)],[c_605]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1636,plain,
% 1.40/1.00      ( ~ r1_tarski(k2_struct_0(sK2),X0_47)
% 1.40/1.00      | r2_hidden(k2_struct_0(sK2),sK4)
% 1.40/1.00      | ~ r2_hidden(sK3,k2_struct_0(sK2))
% 1.40/1.00      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X0_47) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_606]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1652,plain,
% 1.40/1.00      ( ~ r1_tarski(k2_struct_0(sK2),X0_47)
% 1.40/1.00      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X0_47)
% 1.40/1.00      | ~ sP0_iProver_split ),
% 1.40/1.00      inference(splitting,
% 1.40/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.40/1.00                [c_1636]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2018,plain,
% 1.40/1.00      ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X0_47)
% 1.40/1.00      | r1_tarski(k2_struct_0(sK2),X0_47) != iProver_top
% 1.40/1.00      | sP0_iProver_split != iProver_top ),
% 1.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1652]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_10,plain,
% 1.40/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.40/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_9,plain,
% 1.40/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.40/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_320,plain,
% 1.40/1.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.40/1.00      inference(resolution,[status(thm)],[c_10,c_9]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_360,plain,
% 1.40/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 1.40/1.00      inference(resolution_lifted,[status(thm)],[c_320,c_21]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_361,plain,
% 1.40/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.40/1.00      inference(unflattening,[status(thm)],[c_360]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1643,plain,
% 1.40/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_361]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2085,plain,
% 1.40/1.00      ( k1_zfmisc_1(k2_struct_0(sK2)) != k1_zfmisc_1(X0_47)
% 1.40/1.00      | r1_tarski(k2_struct_0(sK2),X0_47) != iProver_top
% 1.40/1.00      | sP0_iProver_split != iProver_top ),
% 1.40/1.00      inference(light_normalisation,[status(thm)],[c_2018,c_1643]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2695,plain,
% 1.40/1.00      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) != iProver_top
% 1.40/1.00      | sP0_iProver_split != iProver_top ),
% 1.40/1.00      inference(equality_resolution,[status(thm)],[c_2085]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_5,plain,
% 1.40/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.40/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_65,plain,
% 1.40/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.40/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1660,plain,
% 1.40/1.00      ( X0_47 != X1_47 | k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47) ),
% 1.40/1.00      theory(equality) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2362,plain,
% 1.40/1.00      ( u1_struct_0(sK2) != X0_47
% 1.40/1.00      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(X0_47) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1660]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2585,plain,
% 1.40/1.00      ( u1_struct_0(sK2) != k2_struct_0(sK2)
% 1.40/1.00      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(k2_struct_0(sK2)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_2362]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2657,plain,
% 1.40/1.00      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))
% 1.40/1.00      | ~ sP0_iProver_split
% 1.40/1.00      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(k2_struct_0(sK2)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1652]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2658,plain,
% 1.40/1.00      ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(k2_struct_0(sK2))
% 1.40/1.00      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) != iProver_top
% 1.40/1.00      | sP0_iProver_split != iProver_top ),
% 1.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2657]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1653,plain,
% 1.40/1.00      ( r2_hidden(k2_struct_0(sK2),sK4)
% 1.40/1.00      | ~ r2_hidden(sK3,k2_struct_0(sK2))
% 1.40/1.00      | sP0_iProver_split ),
% 1.40/1.00      inference(splitting,
% 1.40/1.00                [splitting(split),new_symbols(definition,[])],
% 1.40/1.00                [c_1636]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2017,plain,
% 1.40/1.00      ( r2_hidden(k2_struct_0(sK2),sK4) = iProver_top
% 1.40/1.00      | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top
% 1.40/1.00      | sP0_iProver_split = iProver_top ),
% 1.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1653]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_14,negated_conjecture,
% 1.40/1.00      ( k1_xboole_0 = sK4 ),
% 1.40/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1645,negated_conjecture,
% 1.40/1.00      ( k1_xboole_0 = sK4 ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2066,plain,
% 1.40/1.00      ( r2_hidden(k2_struct_0(sK2),k1_xboole_0) = iProver_top
% 1.40/1.00      | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top
% 1.40/1.00      | sP0_iProver_split = iProver_top ),
% 1.40/1.00      inference(light_normalisation,[status(thm)],[c_2017,c_1645]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_6,plain,
% 1.40/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.40/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_20,negated_conjecture,
% 1.40/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.40/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_552,plain,
% 1.40/1.00      ( r2_hidden(X0,X1)
% 1.40/1.00      | v1_xboole_0(X1)
% 1.40/1.00      | u1_struct_0(sK2) != X1
% 1.40/1.00      | sK3 != X0 ),
% 1.40/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_553,plain,
% 1.40/1.00      ( r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.40/1.00      inference(unflattening,[status(thm)],[c_552]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_23,negated_conjecture,
% 1.40/1.00      ( ~ v2_struct_0(sK2) ),
% 1.40/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_11,plain,
% 1.40/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.40/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_48,plain,
% 1.40/1.00      ( v2_struct_0(sK2)
% 1.40/1.00      | ~ l1_struct_0(sK2)
% 1.40/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_51,plain,
% 1.40/1.00      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_555,plain,
% 1.40/1.00      ( r2_hidden(sK3,u1_struct_0(sK2)) ),
% 1.40/1.00      inference(global_propositional_subsumption,
% 1.40/1.00                [status(thm)],
% 1.40/1.00                [c_553,c_23,c_21,c_48,c_51]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1640,plain,
% 1.40/1.00      ( r2_hidden(sK3,u1_struct_0(sK2)) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_555]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2013,plain,
% 1.40/1.00      ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1640]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2032,plain,
% 1.40/1.00      ( r2_hidden(sK3,k2_struct_0(sK2)) = iProver_top ),
% 1.40/1.00      inference(light_normalisation,[status(thm)],[c_2013,c_1643]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2070,plain,
% 1.40/1.00      ( r2_hidden(k2_struct_0(sK2),k1_xboole_0) = iProver_top
% 1.40/1.00      | sP0_iProver_split = iProver_top ),
% 1.40/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2066,c_2032]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1,plain,
% 1.40/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.40/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1650,plain,
% 1.40/1.00      ( ~ r2_hidden(X0_47,X1_47) | ~ v1_xboole_0(X1_47) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2005,plain,
% 1.40/1.00      ( r2_hidden(X0_47,X1_47) != iProver_top
% 1.40/1.00      | v1_xboole_0(X1_47) != iProver_top ),
% 1.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2813,plain,
% 1.40/1.00      ( v1_xboole_0(k1_xboole_0) != iProver_top
% 1.40/1.00      | sP0_iProver_split = iProver_top ),
% 1.40/1.00      inference(superposition,[status(thm)],[c_2070,c_2005]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_3116,plain,
% 1.40/1.00      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) != iProver_top ),
% 1.40/1.00      inference(global_propositional_subsumption,
% 1.40/1.00                [status(thm)],
% 1.40/1.00                [c_2695,c_65,c_1643,c_2585,c_2658,c_2813]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_3,plain,
% 1.40/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.40/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1648,plain,
% 1.40/1.00      ( r1_tarski(X0_47,X1_47) | r2_hidden(sK1(X0_47,X1_47),X0_47) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2007,plain,
% 1.40/1.00      ( r1_tarski(X0_47,X1_47) = iProver_top
% 1.40/1.00      | r2_hidden(sK1(X0_47,X1_47),X0_47) = iProver_top ),
% 1.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2,plain,
% 1.40/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 1.40/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1649,plain,
% 1.40/1.00      ( r1_tarski(X0_47,X1_47) | ~ r2_hidden(sK1(X0_47,X1_47),X1_47) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2006,plain,
% 1.40/1.00      ( r1_tarski(X0_47,X1_47) = iProver_top
% 1.40/1.00      | r2_hidden(sK1(X0_47,X1_47),X1_47) != iProver_top ),
% 1.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1649]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_2532,plain,
% 1.40/1.00      ( r1_tarski(X0_47,X0_47) = iProver_top ),
% 1.40/1.00      inference(superposition,[status(thm)],[c_2007,c_2006]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_3121,plain,
% 1.40/1.00      ( $false ),
% 1.40/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3116,c_2532]) ).
% 1.40/1.00  
% 1.40/1.00  
% 1.40/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.40/1.00  
% 1.40/1.00  ------                               Statistics
% 1.40/1.00  
% 1.40/1.00  ------ General
% 1.40/1.00  
% 1.40/1.00  abstr_ref_over_cycles:                  0
% 1.40/1.00  abstr_ref_under_cycles:                 0
% 1.40/1.00  gc_basic_clause_elim:                   0
% 1.40/1.00  forced_gc_time:                         0
% 1.40/1.00  parsing_time:                           0.008
% 1.40/1.00  unif_index_cands_time:                  0.
% 1.40/1.00  unif_index_add_time:                    0.
% 1.40/1.00  orderings_time:                         0.
% 1.40/1.00  out_proof_time:                         0.009
% 1.40/1.00  total_time:                             0.104
% 1.40/1.00  num_of_symbols:                         53
% 1.40/1.00  num_of_terms:                           1738
% 1.40/1.00  
% 1.40/1.00  ------ Preprocessing
% 1.40/1.00  
% 1.40/1.00  num_of_splits:                          1
% 1.40/1.00  num_of_split_atoms:                     1
% 1.40/1.00  num_of_reused_defs:                     0
% 1.40/1.00  num_eq_ax_congr_red:                    17
% 1.40/1.00  num_of_sem_filtered_clauses:            1
% 1.40/1.00  num_of_subtypes:                        2
% 1.40/1.00  monotx_restored_types:                  0
% 1.40/1.00  sat_num_of_epr_types:                   0
% 1.40/1.00  sat_num_of_non_cyclic_types:            0
% 1.40/1.00  sat_guarded_non_collapsed_types:        0
% 1.40/1.00  num_pure_diseq_elim:                    0
% 1.40/1.00  simp_replaced_by:                       0
% 1.40/1.00  res_preprocessed:                       99
% 1.40/1.00  prep_upred:                             0
% 1.40/1.00  prep_unflattend:                        67
% 1.40/1.00  smt_new_axioms:                         0
% 1.40/1.00  pred_elim_cands:                        3
% 1.40/1.00  pred_elim:                              7
% 1.40/1.00  pred_elim_cl:                           4
% 1.40/1.00  pred_elim_cycles:                       13
% 1.40/1.00  merged_defs:                            2
% 1.40/1.00  merged_defs_ncl:                        0
% 1.40/1.00  bin_hyper_res:                          2
% 1.40/1.00  prep_cycles:                            4
% 1.40/1.00  pred_elim_time:                         0.018
% 1.40/1.00  splitting_time:                         0.
% 1.40/1.00  sem_filter_time:                        0.
% 1.40/1.00  monotx_time:                            0.
% 1.40/1.00  subtype_inf_time:                       0.
% 1.40/1.00  
% 1.40/1.00  ------ Problem properties
% 1.40/1.00  
% 1.40/1.00  clauses:                                21
% 1.40/1.00  conjectures:                            1
% 1.40/1.00  epr:                                    4
% 1.40/1.00  horn:                                   16
% 1.40/1.00  ground:                                 11
% 1.40/1.00  unary:                                  5
% 1.40/1.00  binary:                                 7
% 1.40/1.00  lits:                                   49
% 1.40/1.00  lits_eq:                                12
% 1.40/1.00  fd_pure:                                0
% 1.40/1.00  fd_pseudo:                              0
% 1.40/1.00  fd_cond:                                0
% 1.40/1.00  fd_pseudo_cond:                         0
% 1.40/1.00  ac_symbols:                             0
% 1.40/1.00  
% 1.40/1.00  ------ Propositional Solver
% 1.40/1.00  
% 1.40/1.00  prop_solver_calls:                      27
% 1.40/1.00  prop_fast_solver_calls:                 741
% 1.40/1.00  smt_solver_calls:                       0
% 1.40/1.00  smt_fast_solver_calls:                  0
% 1.40/1.00  prop_num_of_clauses:                    800
% 1.40/1.00  prop_preprocess_simplified:             3326
% 1.40/1.00  prop_fo_subsumed:                       9
% 1.40/1.00  prop_solver_time:                       0.
% 1.40/1.00  smt_solver_time:                        0.
% 1.40/1.00  smt_fast_solver_time:                   0.
% 1.40/1.00  prop_fast_solver_time:                  0.
% 1.40/1.00  prop_unsat_core_time:                   0.
% 1.40/1.00  
% 1.40/1.00  ------ QBF
% 1.40/1.00  
% 1.40/1.00  qbf_q_res:                              0
% 1.40/1.00  qbf_num_tautologies:                    0
% 1.40/1.00  qbf_prep_cycles:                        0
% 1.40/1.00  
% 1.40/1.00  ------ BMC1
% 1.40/1.00  
% 1.40/1.00  bmc1_current_bound:                     -1
% 1.40/1.00  bmc1_last_solved_bound:                 -1
% 1.40/1.00  bmc1_unsat_core_size:                   -1
% 1.40/1.00  bmc1_unsat_core_parents_size:           -1
% 1.40/1.00  bmc1_merge_next_fun:                    0
% 1.40/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.40/1.00  
% 1.40/1.00  ------ Instantiation
% 1.40/1.00  
% 1.40/1.00  inst_num_of_clauses:                    189
% 1.40/1.00  inst_num_in_passive:                    50
% 1.40/1.00  inst_num_in_active:                     124
% 1.40/1.00  inst_num_in_unprocessed:                15
% 1.40/1.00  inst_num_of_loops:                      140
% 1.40/1.00  inst_num_of_learning_restarts:          0
% 1.40/1.00  inst_num_moves_active_passive:          13
% 1.40/1.00  inst_lit_activity:                      0
% 1.40/1.00  inst_lit_activity_moves:                0
% 1.40/1.00  inst_num_tautologies:                   0
% 1.40/1.00  inst_num_prop_implied:                  0
% 1.40/1.00  inst_num_existing_simplified:           0
% 1.40/1.00  inst_num_eq_res_simplified:             0
% 1.40/1.00  inst_num_child_elim:                    0
% 1.40/1.00  inst_num_of_dismatching_blockings:      34
% 1.40/1.00  inst_num_of_non_proper_insts:           177
% 1.40/1.00  inst_num_of_duplicates:                 0
% 1.40/1.00  inst_inst_num_from_inst_to_res:         0
% 1.40/1.00  inst_dismatching_checking_time:         0.
% 1.40/1.00  
% 1.40/1.00  ------ Resolution
% 1.40/1.00  
% 1.40/1.00  res_num_of_clauses:                     0
% 1.40/1.00  res_num_in_passive:                     0
% 1.40/1.00  res_num_in_active:                      0
% 1.40/1.00  res_num_of_loops:                       103
% 1.40/1.00  res_forward_subset_subsumed:            19
% 1.40/1.00  res_backward_subset_subsumed:           0
% 1.40/1.00  res_forward_subsumed:                   0
% 1.40/1.00  res_backward_subsumed:                  0
% 1.40/1.00  res_forward_subsumption_resolution:     0
% 1.40/1.00  res_backward_subsumption_resolution:    0
% 1.40/1.00  res_clause_to_clause_subsumption:       137
% 1.40/1.00  res_orphan_elimination:                 0
% 1.40/1.00  res_tautology_del:                      27
% 1.40/1.00  res_num_eq_res_simplified:              0
% 1.40/1.00  res_num_sel_changes:                    0
% 1.40/1.00  res_moves_from_active_to_pass:          0
% 1.40/1.00  
% 1.40/1.00  ------ Superposition
% 1.40/1.00  
% 1.40/1.00  sup_time_total:                         0.
% 1.40/1.00  sup_time_generating:                    0.
% 1.40/1.00  sup_time_sim_full:                      0.
% 1.40/1.00  sup_time_sim_immed:                     0.
% 1.40/1.00  
% 1.40/1.00  sup_num_of_clauses:                     30
% 1.40/1.00  sup_num_in_active:                      26
% 1.40/1.00  sup_num_in_passive:                     4
% 1.40/1.00  sup_num_of_loops:                       26
% 1.40/1.00  sup_fw_superposition:                   4
% 1.40/1.00  sup_bw_superposition:                   9
% 1.40/1.00  sup_immediate_simplified:               2
% 1.40/1.00  sup_given_eliminated:                   0
% 1.40/1.00  comparisons_done:                       0
% 1.40/1.00  comparisons_avoided:                    0
% 1.40/1.00  
% 1.40/1.00  ------ Simplifications
% 1.40/1.00  
% 1.40/1.00  
% 1.40/1.00  sim_fw_subset_subsumed:                 1
% 1.40/1.00  sim_bw_subset_subsumed:                 0
% 1.40/1.00  sim_fw_subsumed:                        1
% 1.40/1.00  sim_bw_subsumed:                        0
% 1.40/1.00  sim_fw_subsumption_res:                 4
% 1.40/1.00  sim_bw_subsumption_res:                 0
% 1.40/1.00  sim_tautology_del:                      3
% 1.40/1.00  sim_eq_tautology_del:                   0
% 1.40/1.00  sim_eq_res_simp:                        0
% 1.40/1.00  sim_fw_demodulated:                     0
% 1.40/1.00  sim_bw_demodulated:                     0
% 1.40/1.00  sim_light_normalised:                   12
% 1.40/1.00  sim_joinable_taut:                      0
% 1.40/1.00  sim_joinable_simp:                      0
% 1.40/1.00  sim_ac_normalised:                      0
% 1.40/1.00  sim_smt_subsumption:                    0
% 1.40/1.00  
%------------------------------------------------------------------------------

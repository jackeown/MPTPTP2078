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
% DateTime   : Thu Dec  3 12:26:01 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 550 expanded)
%              Number of clauses        :   64 ( 113 expanded)
%              Number of leaves         :   23 ( 157 expanded)
%              Depth                    :   19
%              Number of atoms          :  554 (2402 expanded)
%              Number of equality atoms :  155 ( 559 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK6,X1)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK5,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK5)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3)
                  | ~ v4_pre_topc(X3,sK4)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ! [X3] :
        ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
        | ~ v4_pre_topc(X3,sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
    & r2_hidden(sK6,sK5)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f42,f41,f40])).

fof(f76,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f81])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f82])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f84])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v4_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v4_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f82])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f83])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f83])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f89])).

fof(f77,plain,(
    ! [X3] :
      ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    ! [X3] :
      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(definition_unfolding,[],[f77,f84])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK3(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2867,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2869,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1362,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_354,c_1362])).

cnf(c_2857,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_4124,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_2857])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2864,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_485,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_486,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_2861,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_3146,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2864,c_2861])).

cnf(c_27,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_486])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5)
    | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_776,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_3802,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3146,c_27,c_776])).

cnf(c_4122,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK5) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_3802])).

cnf(c_6002,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4124,c_4122])).

cnf(c_3281,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2864,c_2857])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2874,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3567,plain,
    ( k1_setfam_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,u1_struct_0(sK4))) = sK5 ),
    inference(superposition,[status(thm)],[c_3281,c_2874])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2876,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4230,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_2876])).

cnf(c_8411,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6002,c_4230])).

cnf(c_8425,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(superposition,[status(thm)],[c_2867,c_8411])).

cnf(c_20,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2868,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0)
    | v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8637,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8425,c_2868])).

cnf(c_4486,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4489,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4486])).

cnf(c_4491,plain,
    ( m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4489])).

cnf(c_4243,plain,
    ( r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4230])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_464,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_465,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_3071,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,sK5,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_3322,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_3071])).

cnf(c_3326,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3322])).

cnf(c_18,plain,
    ( v4_pre_topc(sK3(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_443,plain,
    ( v4_pre_topc(sK3(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_444,plain,
    ( v4_pre_topc(sK3(sK4,X0,X1),sK4)
    | ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_3068,plain,
    ( v4_pre_topc(sK3(sK4,sK5,X0),sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_3323,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_3068])).

cnf(c_3324,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK4) = iProver_top
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3323])).

cnf(c_3153,plain,
    ( ~ m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(sK5))
    | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_3154,plain,
    ( m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3153])).

cnf(c_3118,plain,
    ( m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(sK5))
    | ~ r2_hidden(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3119,plain,
    ( m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(sK5)) = iProver_top
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3118])).

cnf(c_30,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_28,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8637,c_4491,c_4243,c_3326,c_3324,c_3154,c_3119,c_30,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.80/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.97  
% 2.80/0.97  ------  iProver source info
% 2.80/0.97  
% 2.80/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.97  git: non_committed_changes: false
% 2.80/0.97  git: last_make_outside_of_git: false
% 2.80/0.97  
% 2.80/0.97  ------ 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options
% 2.80/0.97  
% 2.80/0.97  --out_options                           all
% 2.80/0.97  --tptp_safe_out                         true
% 2.80/0.97  --problem_path                          ""
% 2.80/0.97  --include_path                          ""
% 2.80/0.97  --clausifier                            res/vclausify_rel
% 2.80/0.97  --clausifier_options                    --mode clausify
% 2.80/0.97  --stdin                                 false
% 2.80/0.97  --stats_out                             all
% 2.80/0.97  
% 2.80/0.97  ------ General Options
% 2.80/0.97  
% 2.80/0.97  --fof                                   false
% 2.80/0.97  --time_out_real                         305.
% 2.80/0.97  --time_out_virtual                      -1.
% 2.80/0.97  --symbol_type_check                     false
% 2.80/0.97  --clausify_out                          false
% 2.80/0.97  --sig_cnt_out                           false
% 2.80/0.97  --trig_cnt_out                          false
% 2.80/0.97  --trig_cnt_out_tolerance                1.
% 2.80/0.97  --trig_cnt_out_sk_spl                   false
% 2.80/0.97  --abstr_cl_out                          false
% 2.80/0.97  
% 2.80/0.97  ------ Global Options
% 2.80/0.97  
% 2.80/0.97  --schedule                              default
% 2.80/0.97  --add_important_lit                     false
% 2.80/0.97  --prop_solver_per_cl                    1000
% 2.80/0.97  --min_unsat_core                        false
% 2.80/0.97  --soft_assumptions                      false
% 2.80/0.97  --soft_lemma_size                       3
% 2.80/0.97  --prop_impl_unit_size                   0
% 2.80/0.97  --prop_impl_unit                        []
% 2.80/0.97  --share_sel_clauses                     true
% 2.80/0.97  --reset_solvers                         false
% 2.80/0.97  --bc_imp_inh                            [conj_cone]
% 2.80/0.97  --conj_cone_tolerance                   3.
% 2.80/0.97  --extra_neg_conj                        none
% 2.80/0.97  --large_theory_mode                     true
% 2.80/0.97  --prolific_symb_bound                   200
% 2.80/0.97  --lt_threshold                          2000
% 2.80/0.97  --clause_weak_htbl                      true
% 2.80/0.97  --gc_record_bc_elim                     false
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing Options
% 2.80/0.97  
% 2.80/0.97  --preprocessing_flag                    true
% 2.80/0.97  --time_out_prep_mult                    0.1
% 2.80/0.97  --splitting_mode                        input
% 2.80/0.97  --splitting_grd                         true
% 2.80/0.97  --splitting_cvd                         false
% 2.80/0.97  --splitting_cvd_svl                     false
% 2.80/0.97  --splitting_nvd                         32
% 2.80/0.97  --sub_typing                            true
% 2.80/0.97  --prep_gs_sim                           true
% 2.80/0.97  --prep_unflatten                        true
% 2.80/0.97  --prep_res_sim                          true
% 2.80/0.97  --prep_upred                            true
% 2.80/0.97  --prep_sem_filter                       exhaustive
% 2.80/0.97  --prep_sem_filter_out                   false
% 2.80/0.97  --pred_elim                             true
% 2.80/0.97  --res_sim_input                         true
% 2.80/0.97  --eq_ax_congr_red                       true
% 2.80/0.97  --pure_diseq_elim                       true
% 2.80/0.97  --brand_transform                       false
% 2.80/0.97  --non_eq_to_eq                          false
% 2.80/0.97  --prep_def_merge                        true
% 2.80/0.97  --prep_def_merge_prop_impl              false
% 2.80/0.97  --prep_def_merge_mbd                    true
% 2.80/0.97  --prep_def_merge_tr_red                 false
% 2.80/0.97  --prep_def_merge_tr_cl                  false
% 2.80/0.97  --smt_preprocessing                     true
% 2.80/0.97  --smt_ac_axioms                         fast
% 2.80/0.97  --preprocessed_out                      false
% 2.80/0.97  --preprocessed_stats                    false
% 2.80/0.97  
% 2.80/0.97  ------ Abstraction refinement Options
% 2.80/0.97  
% 2.80/0.97  --abstr_ref                             []
% 2.80/0.97  --abstr_ref_prep                        false
% 2.80/0.97  --abstr_ref_until_sat                   false
% 2.80/0.97  --abstr_ref_sig_restrict                funpre
% 2.80/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.97  --abstr_ref_under                       []
% 2.80/0.97  
% 2.80/0.97  ------ SAT Options
% 2.80/0.97  
% 2.80/0.97  --sat_mode                              false
% 2.80/0.97  --sat_fm_restart_options                ""
% 2.80/0.97  --sat_gr_def                            false
% 2.80/0.97  --sat_epr_types                         true
% 2.80/0.97  --sat_non_cyclic_types                  false
% 2.80/0.97  --sat_finite_models                     false
% 2.80/0.97  --sat_fm_lemmas                         false
% 2.80/0.97  --sat_fm_prep                           false
% 2.80/0.97  --sat_fm_uc_incr                        true
% 2.80/0.97  --sat_out_model                         small
% 2.80/0.97  --sat_out_clauses                       false
% 2.80/0.97  
% 2.80/0.97  ------ QBF Options
% 2.80/0.97  
% 2.80/0.97  --qbf_mode                              false
% 2.80/0.97  --qbf_elim_univ                         false
% 2.80/0.97  --qbf_dom_inst                          none
% 2.80/0.97  --qbf_dom_pre_inst                      false
% 2.80/0.97  --qbf_sk_in                             false
% 2.80/0.97  --qbf_pred_elim                         true
% 2.80/0.97  --qbf_split                             512
% 2.80/0.97  
% 2.80/0.97  ------ BMC1 Options
% 2.80/0.97  
% 2.80/0.97  --bmc1_incremental                      false
% 2.80/0.97  --bmc1_axioms                           reachable_all
% 2.80/0.97  --bmc1_min_bound                        0
% 2.80/0.97  --bmc1_max_bound                        -1
% 2.80/0.97  --bmc1_max_bound_default                -1
% 2.80/0.97  --bmc1_symbol_reachability              true
% 2.80/0.97  --bmc1_property_lemmas                  false
% 2.80/0.97  --bmc1_k_induction                      false
% 2.80/0.97  --bmc1_non_equiv_states                 false
% 2.80/0.97  --bmc1_deadlock                         false
% 2.80/0.97  --bmc1_ucm                              false
% 2.80/0.97  --bmc1_add_unsat_core                   none
% 2.80/0.97  --bmc1_unsat_core_children              false
% 2.80/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.97  --bmc1_out_stat                         full
% 2.80/0.97  --bmc1_ground_init                      false
% 2.80/0.97  --bmc1_pre_inst_next_state              false
% 2.80/0.97  --bmc1_pre_inst_state                   false
% 2.80/0.97  --bmc1_pre_inst_reach_state             false
% 2.80/0.97  --bmc1_out_unsat_core                   false
% 2.80/0.97  --bmc1_aig_witness_out                  false
% 2.80/0.97  --bmc1_verbose                          false
% 2.80/0.97  --bmc1_dump_clauses_tptp                false
% 2.80/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.97  --bmc1_dump_file                        -
% 2.80/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.97  --bmc1_ucm_extend_mode                  1
% 2.80/0.97  --bmc1_ucm_init_mode                    2
% 2.80/0.97  --bmc1_ucm_cone_mode                    none
% 2.80/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.97  --bmc1_ucm_relax_model                  4
% 2.80/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.97  --bmc1_ucm_layered_model                none
% 2.80/0.97  --bmc1_ucm_max_lemma_size               10
% 2.80/0.97  
% 2.80/0.97  ------ AIG Options
% 2.80/0.97  
% 2.80/0.97  --aig_mode                              false
% 2.80/0.97  
% 2.80/0.97  ------ Instantiation Options
% 2.80/0.97  
% 2.80/0.97  --instantiation_flag                    true
% 2.80/0.97  --inst_sos_flag                         false
% 2.80/0.97  --inst_sos_phase                        true
% 2.80/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel_side                     num_symb
% 2.80/0.97  --inst_solver_per_active                1400
% 2.80/0.97  --inst_solver_calls_frac                1.
% 2.80/0.97  --inst_passive_queue_type               priority_queues
% 2.80/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.97  --inst_passive_queues_freq              [25;2]
% 2.80/0.97  --inst_dismatching                      true
% 2.80/0.97  --inst_eager_unprocessed_to_passive     true
% 2.80/0.97  --inst_prop_sim_given                   true
% 2.80/0.97  --inst_prop_sim_new                     false
% 2.80/0.97  --inst_subs_new                         false
% 2.80/0.97  --inst_eq_res_simp                      false
% 2.80/0.97  --inst_subs_given                       false
% 2.80/0.97  --inst_orphan_elimination               true
% 2.80/0.97  --inst_learning_loop_flag               true
% 2.80/0.97  --inst_learning_start                   3000
% 2.80/0.97  --inst_learning_factor                  2
% 2.80/0.97  --inst_start_prop_sim_after_learn       3
% 2.80/0.97  --inst_sel_renew                        solver
% 2.80/0.97  --inst_lit_activity_flag                true
% 2.80/0.97  --inst_restr_to_given                   false
% 2.80/0.97  --inst_activity_threshold               500
% 2.80/0.97  --inst_out_proof                        true
% 2.80/0.97  
% 2.80/0.97  ------ Resolution Options
% 2.80/0.97  
% 2.80/0.97  --resolution_flag                       true
% 2.80/0.97  --res_lit_sel                           adaptive
% 2.80/0.97  --res_lit_sel_side                      none
% 2.80/0.97  --res_ordering                          kbo
% 2.80/0.97  --res_to_prop_solver                    active
% 2.80/0.97  --res_prop_simpl_new                    false
% 2.80/0.97  --res_prop_simpl_given                  true
% 2.80/0.97  --res_passive_queue_type                priority_queues
% 2.80/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.97  --res_passive_queues_freq               [15;5]
% 2.80/0.97  --res_forward_subs                      full
% 2.80/0.97  --res_backward_subs                     full
% 2.80/0.97  --res_forward_subs_resolution           true
% 2.80/0.97  --res_backward_subs_resolution          true
% 2.80/0.97  --res_orphan_elimination                true
% 2.80/0.97  --res_time_limit                        2.
% 2.80/0.97  --res_out_proof                         true
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Options
% 2.80/0.97  
% 2.80/0.97  --superposition_flag                    true
% 2.80/0.97  --sup_passive_queue_type                priority_queues
% 2.80/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.97  --demod_completeness_check              fast
% 2.80/0.97  --demod_use_ground                      true
% 2.80/0.97  --sup_to_prop_solver                    passive
% 2.80/0.97  --sup_prop_simpl_new                    true
% 2.80/0.97  --sup_prop_simpl_given                  true
% 2.80/0.97  --sup_fun_splitting                     false
% 2.80/0.97  --sup_smt_interval                      50000
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Simplification Setup
% 2.80/0.97  
% 2.80/0.97  --sup_indices_passive                   []
% 2.80/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_full_bw                           [BwDemod]
% 2.80/0.97  --sup_immed_triv                        [TrivRules]
% 2.80/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_immed_bw_main                     []
% 2.80/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  
% 2.80/0.97  ------ Combination Options
% 2.80/0.97  
% 2.80/0.97  --comb_res_mult                         3
% 2.80/0.97  --comb_sup_mult                         2
% 2.80/0.97  --comb_inst_mult                        10
% 2.80/0.97  
% 2.80/0.97  ------ Debug Options
% 2.80/0.97  
% 2.80/0.97  --dbg_backtrace                         false
% 2.80/0.97  --dbg_dump_prop_clauses                 false
% 2.80/0.97  --dbg_dump_prop_clauses_file            -
% 2.80/0.97  --dbg_out_stat                          false
% 2.80/0.97  ------ Parsing...
% 2.80/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/0.97  ------ Proving...
% 2.80/0.97  ------ Problem Properties 
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  clauses                                 24
% 2.80/0.97  conjectures                             5
% 2.80/0.97  EPR                                     2
% 2.80/0.97  Horn                                    19
% 2.80/0.97  unary                                   4
% 2.80/0.97  binary                                  7
% 2.80/0.97  lits                                    66
% 2.80/0.97  lits eq                                 9
% 2.80/0.97  fd_pure                                 0
% 2.80/0.97  fd_pseudo                               0
% 2.80/0.97  fd_cond                                 0
% 2.80/0.97  fd_pseudo_cond                          5
% 2.80/0.97  AC symbols                              0
% 2.80/0.97  
% 2.80/0.97  ------ Schedule dynamic 5 is on 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  ------ 
% 2.80/0.97  Current options:
% 2.80/0.97  ------ 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options
% 2.80/0.97  
% 2.80/0.97  --out_options                           all
% 2.80/0.97  --tptp_safe_out                         true
% 2.80/0.97  --problem_path                          ""
% 2.80/0.97  --include_path                          ""
% 2.80/0.97  --clausifier                            res/vclausify_rel
% 2.80/0.97  --clausifier_options                    --mode clausify
% 2.80/0.97  --stdin                                 false
% 2.80/0.97  --stats_out                             all
% 2.80/0.97  
% 2.80/0.97  ------ General Options
% 2.80/0.97  
% 2.80/0.97  --fof                                   false
% 2.80/0.97  --time_out_real                         305.
% 2.80/0.97  --time_out_virtual                      -1.
% 2.80/0.97  --symbol_type_check                     false
% 2.80/0.97  --clausify_out                          false
% 2.80/0.97  --sig_cnt_out                           false
% 2.80/0.97  --trig_cnt_out                          false
% 2.80/0.97  --trig_cnt_out_tolerance                1.
% 2.80/0.97  --trig_cnt_out_sk_spl                   false
% 2.80/0.97  --abstr_cl_out                          false
% 2.80/0.97  
% 2.80/0.97  ------ Global Options
% 2.80/0.97  
% 2.80/0.97  --schedule                              default
% 2.80/0.97  --add_important_lit                     false
% 2.80/0.97  --prop_solver_per_cl                    1000
% 2.80/0.97  --min_unsat_core                        false
% 2.80/0.97  --soft_assumptions                      false
% 2.80/0.97  --soft_lemma_size                       3
% 2.80/0.97  --prop_impl_unit_size                   0
% 2.80/0.97  --prop_impl_unit                        []
% 2.80/0.97  --share_sel_clauses                     true
% 2.80/0.97  --reset_solvers                         false
% 2.80/0.97  --bc_imp_inh                            [conj_cone]
% 2.80/0.97  --conj_cone_tolerance                   3.
% 2.80/0.97  --extra_neg_conj                        none
% 2.80/0.97  --large_theory_mode                     true
% 2.80/0.97  --prolific_symb_bound                   200
% 2.80/0.97  --lt_threshold                          2000
% 2.80/0.97  --clause_weak_htbl                      true
% 2.80/0.97  --gc_record_bc_elim                     false
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing Options
% 2.80/0.97  
% 2.80/0.97  --preprocessing_flag                    true
% 2.80/0.97  --time_out_prep_mult                    0.1
% 2.80/0.97  --splitting_mode                        input
% 2.80/0.97  --splitting_grd                         true
% 2.80/0.97  --splitting_cvd                         false
% 2.80/0.97  --splitting_cvd_svl                     false
% 2.80/0.97  --splitting_nvd                         32
% 2.80/0.97  --sub_typing                            true
% 2.80/0.97  --prep_gs_sim                           true
% 2.80/0.97  --prep_unflatten                        true
% 2.80/0.97  --prep_res_sim                          true
% 2.80/0.97  --prep_upred                            true
% 2.80/0.97  --prep_sem_filter                       exhaustive
% 2.80/0.97  --prep_sem_filter_out                   false
% 2.80/0.97  --pred_elim                             true
% 2.80/0.97  --res_sim_input                         true
% 2.80/0.97  --eq_ax_congr_red                       true
% 2.80/0.97  --pure_diseq_elim                       true
% 2.80/0.97  --brand_transform                       false
% 2.80/0.97  --non_eq_to_eq                          false
% 2.80/0.97  --prep_def_merge                        true
% 2.80/0.97  --prep_def_merge_prop_impl              false
% 2.80/0.97  --prep_def_merge_mbd                    true
% 2.80/0.97  --prep_def_merge_tr_red                 false
% 2.80/0.97  --prep_def_merge_tr_cl                  false
% 2.80/0.97  --smt_preprocessing                     true
% 2.80/0.97  --smt_ac_axioms                         fast
% 2.80/0.97  --preprocessed_out                      false
% 2.80/0.97  --preprocessed_stats                    false
% 2.80/0.97  
% 2.80/0.97  ------ Abstraction refinement Options
% 2.80/0.97  
% 2.80/0.97  --abstr_ref                             []
% 2.80/0.97  --abstr_ref_prep                        false
% 2.80/0.97  --abstr_ref_until_sat                   false
% 2.80/0.97  --abstr_ref_sig_restrict                funpre
% 2.80/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.97  --abstr_ref_under                       []
% 2.80/0.97  
% 2.80/0.97  ------ SAT Options
% 2.80/0.97  
% 2.80/0.97  --sat_mode                              false
% 2.80/0.97  --sat_fm_restart_options                ""
% 2.80/0.97  --sat_gr_def                            false
% 2.80/0.97  --sat_epr_types                         true
% 2.80/0.97  --sat_non_cyclic_types                  false
% 2.80/0.97  --sat_finite_models                     false
% 2.80/0.97  --sat_fm_lemmas                         false
% 2.80/0.97  --sat_fm_prep                           false
% 2.80/0.97  --sat_fm_uc_incr                        true
% 2.80/0.97  --sat_out_model                         small
% 2.80/0.97  --sat_out_clauses                       false
% 2.80/0.97  
% 2.80/0.97  ------ QBF Options
% 2.80/0.97  
% 2.80/0.97  --qbf_mode                              false
% 2.80/0.97  --qbf_elim_univ                         false
% 2.80/0.97  --qbf_dom_inst                          none
% 2.80/0.97  --qbf_dom_pre_inst                      false
% 2.80/0.97  --qbf_sk_in                             false
% 2.80/0.97  --qbf_pred_elim                         true
% 2.80/0.97  --qbf_split                             512
% 2.80/0.97  
% 2.80/0.97  ------ BMC1 Options
% 2.80/0.97  
% 2.80/0.97  --bmc1_incremental                      false
% 2.80/0.97  --bmc1_axioms                           reachable_all
% 2.80/0.97  --bmc1_min_bound                        0
% 2.80/0.97  --bmc1_max_bound                        -1
% 2.80/0.97  --bmc1_max_bound_default                -1
% 2.80/0.97  --bmc1_symbol_reachability              true
% 2.80/0.97  --bmc1_property_lemmas                  false
% 2.80/0.97  --bmc1_k_induction                      false
% 2.80/0.97  --bmc1_non_equiv_states                 false
% 2.80/0.97  --bmc1_deadlock                         false
% 2.80/0.97  --bmc1_ucm                              false
% 2.80/0.97  --bmc1_add_unsat_core                   none
% 2.80/0.97  --bmc1_unsat_core_children              false
% 2.80/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.97  --bmc1_out_stat                         full
% 2.80/0.97  --bmc1_ground_init                      false
% 2.80/0.97  --bmc1_pre_inst_next_state              false
% 2.80/0.97  --bmc1_pre_inst_state                   false
% 2.80/0.97  --bmc1_pre_inst_reach_state             false
% 2.80/0.97  --bmc1_out_unsat_core                   false
% 2.80/0.97  --bmc1_aig_witness_out                  false
% 2.80/0.97  --bmc1_verbose                          false
% 2.80/0.97  --bmc1_dump_clauses_tptp                false
% 2.80/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.97  --bmc1_dump_file                        -
% 2.80/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.97  --bmc1_ucm_extend_mode                  1
% 2.80/0.97  --bmc1_ucm_init_mode                    2
% 2.80/0.97  --bmc1_ucm_cone_mode                    none
% 2.80/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.97  --bmc1_ucm_relax_model                  4
% 2.80/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.97  --bmc1_ucm_layered_model                none
% 2.80/0.97  --bmc1_ucm_max_lemma_size               10
% 2.80/0.97  
% 2.80/0.97  ------ AIG Options
% 2.80/0.97  
% 2.80/0.97  --aig_mode                              false
% 2.80/0.97  
% 2.80/0.97  ------ Instantiation Options
% 2.80/0.97  
% 2.80/0.97  --instantiation_flag                    true
% 2.80/0.97  --inst_sos_flag                         false
% 2.80/0.97  --inst_sos_phase                        true
% 2.80/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel_side                     none
% 2.80/0.97  --inst_solver_per_active                1400
% 2.80/0.97  --inst_solver_calls_frac                1.
% 2.80/0.97  --inst_passive_queue_type               priority_queues
% 2.80/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.97  --inst_passive_queues_freq              [25;2]
% 2.80/0.97  --inst_dismatching                      true
% 2.80/0.97  --inst_eager_unprocessed_to_passive     true
% 2.80/0.97  --inst_prop_sim_given                   true
% 2.80/0.97  --inst_prop_sim_new                     false
% 2.80/0.97  --inst_subs_new                         false
% 2.80/0.97  --inst_eq_res_simp                      false
% 2.80/0.97  --inst_subs_given                       false
% 2.80/0.97  --inst_orphan_elimination               true
% 2.80/0.97  --inst_learning_loop_flag               true
% 2.80/0.97  --inst_learning_start                   3000
% 2.80/0.97  --inst_learning_factor                  2
% 2.80/0.97  --inst_start_prop_sim_after_learn       3
% 2.80/0.97  --inst_sel_renew                        solver
% 2.80/0.97  --inst_lit_activity_flag                true
% 2.80/0.97  --inst_restr_to_given                   false
% 2.80/0.97  --inst_activity_threshold               500
% 2.80/0.97  --inst_out_proof                        true
% 2.80/0.97  
% 2.80/0.97  ------ Resolution Options
% 2.80/0.97  
% 2.80/0.97  --resolution_flag                       false
% 2.80/0.97  --res_lit_sel                           adaptive
% 2.80/0.97  --res_lit_sel_side                      none
% 2.80/0.97  --res_ordering                          kbo
% 2.80/0.97  --res_to_prop_solver                    active
% 2.80/0.97  --res_prop_simpl_new                    false
% 2.80/0.97  --res_prop_simpl_given                  true
% 2.80/0.97  --res_passive_queue_type                priority_queues
% 2.80/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.97  --res_passive_queues_freq               [15;5]
% 2.80/0.97  --res_forward_subs                      full
% 2.80/0.97  --res_backward_subs                     full
% 2.80/0.97  --res_forward_subs_resolution           true
% 2.80/0.97  --res_backward_subs_resolution          true
% 2.80/0.97  --res_orphan_elimination                true
% 2.80/0.97  --res_time_limit                        2.
% 2.80/0.97  --res_out_proof                         true
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Options
% 2.80/0.97  
% 2.80/0.97  --superposition_flag                    true
% 2.80/0.97  --sup_passive_queue_type                priority_queues
% 2.80/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.97  --demod_completeness_check              fast
% 2.80/0.97  --demod_use_ground                      true
% 2.80/0.97  --sup_to_prop_solver                    passive
% 2.80/0.97  --sup_prop_simpl_new                    true
% 2.80/0.97  --sup_prop_simpl_given                  true
% 2.80/0.97  --sup_fun_splitting                     false
% 2.80/0.97  --sup_smt_interval                      50000
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Simplification Setup
% 2.80/0.97  
% 2.80/0.97  --sup_indices_passive                   []
% 2.80/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_full_bw                           [BwDemod]
% 2.80/0.97  --sup_immed_triv                        [TrivRules]
% 2.80/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_immed_bw_main                     []
% 2.80/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  
% 2.80/0.97  ------ Combination Options
% 2.80/0.97  
% 2.80/0.97  --comb_res_mult                         3
% 2.80/0.97  --comb_sup_mult                         2
% 2.80/0.97  --comb_inst_mult                        10
% 2.80/0.97  
% 2.80/0.97  ------ Debug Options
% 2.80/0.97  
% 2.80/0.97  --dbg_backtrace                         false
% 2.80/0.97  --dbg_dump_prop_clauses                 false
% 2.80/0.97  --dbg_dump_prop_clauses_file            -
% 2.80/0.97  --dbg_out_stat                          false
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  ------ Proving...
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  % SZS status Theorem for theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  fof(f16,conjecture,(
% 2.80/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f17,negated_conjecture,(
% 2.80/0.97    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.80/0.97    inference(negated_conjecture,[],[f16])).
% 2.80/0.97  
% 2.80/0.97  fof(f24,plain,(
% 2.80/0.97    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.80/0.97    inference(ennf_transformation,[],[f17])).
% 2.80/0.97  
% 2.80/0.97  fof(f25,plain,(
% 2.80/0.97    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.80/0.97    inference(flattening,[],[f24])).
% 2.80/0.97  
% 2.80/0.97  fof(f42,plain,(
% 2.80/0.97    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK6,X1) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f41,plain,(
% 2.80/0.97    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK5,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f40,plain,(
% 2.80/0.97    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f43,plain,(
% 2.80/0.97    ((! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f42,f41,f40])).
% 2.80/0.97  
% 2.80/0.97  fof(f76,plain,(
% 2.80/0.97    r2_hidden(sK6,sK5)),
% 2.80/0.97    inference(cnf_transformation,[],[f43])).
% 2.80/0.97  
% 2.80/0.97  fof(f12,axiom,(
% 2.80/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f19,plain,(
% 2.80/0.97    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.80/0.97    inference(ennf_transformation,[],[f12])).
% 2.80/0.97  
% 2.80/0.97  fof(f63,plain,(
% 2.80/0.97    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f19])).
% 2.80/0.97  
% 2.80/0.97  fof(f3,axiom,(
% 2.80/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f51,plain,(
% 2.80/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f3])).
% 2.80/0.97  
% 2.80/0.97  fof(f4,axiom,(
% 2.80/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f52,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f4])).
% 2.80/0.97  
% 2.80/0.97  fof(f5,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f53,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f5])).
% 2.80/0.97  
% 2.80/0.97  fof(f6,axiom,(
% 2.80/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f54,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f6])).
% 2.80/0.97  
% 2.80/0.97  fof(f7,axiom,(
% 2.80/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f55,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f7])).
% 2.80/0.97  
% 2.80/0.97  fof(f8,axiom,(
% 2.80/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f56,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f8])).
% 2.80/0.97  
% 2.80/0.97  fof(f9,axiom,(
% 2.80/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f57,plain,(
% 2.80/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f9])).
% 2.80/0.97  
% 2.80/0.97  fof(f78,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.80/0.97    inference(definition_unfolding,[],[f56,f57])).
% 2.80/0.97  
% 2.80/0.97  fof(f79,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.80/0.97    inference(definition_unfolding,[],[f55,f78])).
% 2.80/0.97  
% 2.80/0.97  fof(f80,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.80/0.97    inference(definition_unfolding,[],[f54,f79])).
% 2.80/0.97  
% 2.80/0.97  fof(f81,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.80/0.97    inference(definition_unfolding,[],[f53,f80])).
% 2.80/0.97  
% 2.80/0.97  fof(f82,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.80/0.97    inference(definition_unfolding,[],[f52,f81])).
% 2.80/0.97  
% 2.80/0.97  fof(f84,plain,(
% 2.80/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.80/0.97    inference(definition_unfolding,[],[f51,f82])).
% 2.80/0.97  
% 2.80/0.97  fof(f92,plain,(
% 2.80/0.97    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.80/0.97    inference(definition_unfolding,[],[f63,f84])).
% 2.80/0.97  
% 2.80/0.97  fof(f11,axiom,(
% 2.80/0.97    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f62,plain,(
% 2.80/0.97    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f11])).
% 2.80/0.97  
% 2.80/0.97  fof(f14,axiom,(
% 2.80/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f20,plain,(
% 2.80/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.80/0.97    inference(ennf_transformation,[],[f14])).
% 2.80/0.97  
% 2.80/0.97  fof(f21,plain,(
% 2.80/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.80/0.97    inference(flattening,[],[f20])).
% 2.80/0.97  
% 2.80/0.97  fof(f65,plain,(
% 2.80/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f21])).
% 2.80/0.97  
% 2.80/0.97  fof(f10,axiom,(
% 2.80/0.97    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f31,plain,(
% 2.80/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.80/0.97    inference(nnf_transformation,[],[f10])).
% 2.80/0.97  
% 2.80/0.97  fof(f32,plain,(
% 2.80/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.80/0.97    inference(rectify,[],[f31])).
% 2.80/0.97  
% 2.80/0.97  fof(f33,plain,(
% 2.80/0.97    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f34,plain,(
% 2.80/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 2.80/0.97  
% 2.80/0.97  fof(f58,plain,(
% 2.80/0.97    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.80/0.97    inference(cnf_transformation,[],[f34])).
% 2.80/0.97  
% 2.80/0.97  fof(f98,plain,(
% 2.80/0.97    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.80/0.97    inference(equality_resolution,[],[f58])).
% 2.80/0.97  
% 2.80/0.97  fof(f73,plain,(
% 2.80/0.97    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.80/0.97    inference(cnf_transformation,[],[f43])).
% 2.80/0.97  
% 2.80/0.97  fof(f15,axiom,(
% 2.80/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f22,plain,(
% 2.80/0.97    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.80/0.97    inference(ennf_transformation,[],[f15])).
% 2.80/0.97  
% 2.80/0.97  fof(f23,plain,(
% 2.80/0.97    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.80/0.97    inference(flattening,[],[f22])).
% 2.80/0.97  
% 2.80/0.97  fof(f35,plain,(
% 2.80/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.80/0.97    inference(nnf_transformation,[],[f23])).
% 2.80/0.97  
% 2.80/0.97  fof(f36,plain,(
% 2.80/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.80/0.97    inference(rectify,[],[f35])).
% 2.80/0.97  
% 2.80/0.97  fof(f38,plain,(
% 2.80/0.97    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f37,plain,(
% 2.80/0.97    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f39,plain,(
% 2.80/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).
% 2.80/0.97  
% 2.80/0.97  fof(f68,plain,(
% 2.80/0.97    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f39])).
% 2.80/0.97  
% 2.80/0.97  fof(f72,plain,(
% 2.80/0.97    l1_pre_topc(sK4)),
% 2.80/0.97    inference(cnf_transformation,[],[f43])).
% 2.80/0.97  
% 2.80/0.97  fof(f74,plain,(
% 2.80/0.97    v2_tex_2(sK5,sK4)),
% 2.80/0.97    inference(cnf_transformation,[],[f43])).
% 2.80/0.97  
% 2.80/0.97  fof(f2,axiom,(
% 2.80/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f18,plain,(
% 2.80/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.80/0.97    inference(ennf_transformation,[],[f2])).
% 2.80/0.97  
% 2.80/0.97  fof(f50,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f18])).
% 2.80/0.97  
% 2.80/0.97  fof(f13,axiom,(
% 2.80/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f64,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f13])).
% 2.80/0.97  
% 2.80/0.97  fof(f83,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.80/0.97    inference(definition_unfolding,[],[f64,f82])).
% 2.80/0.97  
% 2.80/0.97  fof(f91,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.80/0.97    inference(definition_unfolding,[],[f50,f83])).
% 2.80/0.97  
% 2.80/0.97  fof(f1,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.80/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f26,plain,(
% 2.80/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.80/0.97    inference(nnf_transformation,[],[f1])).
% 2.80/0.97  
% 2.80/0.97  fof(f27,plain,(
% 2.80/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.80/0.97    inference(flattening,[],[f26])).
% 2.80/0.97  
% 2.80/0.97  fof(f28,plain,(
% 2.80/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.80/0.97    inference(rectify,[],[f27])).
% 2.80/0.97  
% 2.80/0.97  fof(f29,plain,(
% 2.80/0.97    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f30,plain,(
% 2.80/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.80/0.97  
% 2.80/0.97  fof(f45,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.80/0.97    inference(cnf_transformation,[],[f30])).
% 2.80/0.97  
% 2.80/0.97  fof(f89,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.80/0.97    inference(definition_unfolding,[],[f45,f83])).
% 2.80/0.97  
% 2.80/0.97  fof(f95,plain,(
% 2.80/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.80/0.97    inference(equality_resolution,[],[f89])).
% 2.80/0.97  
% 2.80/0.97  fof(f77,plain,(
% 2.80/0.97    ( ! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f43])).
% 2.80/0.97  
% 2.80/0.97  fof(f93,plain,(
% 2.80/0.97    ( ! [X3] : (k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 2.80/0.97    inference(definition_unfolding,[],[f77,f84])).
% 2.80/0.97  
% 2.80/0.97  fof(f66,plain,(
% 2.80/0.97    ( ! [X4,X0,X1] : (m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f39])).
% 2.80/0.97  
% 2.80/0.97  fof(f67,plain,(
% 2.80/0.97    ( ! [X4,X0,X1] : (v4_pre_topc(sK3(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f39])).
% 2.80/0.97  
% 2.80/0.97  cnf(c_21,negated_conjecture,
% 2.80/0.97      ( r2_hidden(sK6,sK5) ),
% 2.80/0.97      inference(cnf_transformation,[],[f76]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2867,plain,
% 2.80/0.97      ( r2_hidden(sK6,sK5) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_12,plain,
% 2.80/0.97      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 2.80/0.97      | ~ r2_hidden(X0,X1) ),
% 2.80/0.97      inference(cnf_transformation,[],[f92]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2869,plain,
% 2.80/0.97      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.80/0.97      | r2_hidden(X0,X1) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_11,plain,
% 2.80/0.97      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_13,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.80/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_353,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 2.80/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_354,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/0.97      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.80/0.97      inference(unflattening,[status(thm)],[c_353]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_10,plain,
% 2.80/0.97      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f98]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1362,plain,
% 2.80/0.97      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.80/0.97      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1411,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.80/0.97      inference(bin_hyper_res,[status(thm)],[c_354,c_1362]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2857,plain,
% 2.80/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.80/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4124,plain,
% 2.80/0.97      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 2.80/0.97      | r2_hidden(X0,X1) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_2869,c_2857]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_24,negated_conjecture,
% 2.80/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.80/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2864,plain,
% 2.80/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_17,plain,
% 2.80/0.97      ( ~ v2_tex_2(X0,X1)
% 2.80/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.97      | ~ r1_tarski(X2,X0)
% 2.80/0.97      | ~ l1_pre_topc(X1)
% 2.80/0.97      | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2 ),
% 2.80/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_25,negated_conjecture,
% 2.80/0.97      ( l1_pre_topc(sK4) ),
% 2.80/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_485,plain,
% 2.80/0.97      ( ~ v2_tex_2(X0,X1)
% 2.80/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.97      | ~ r1_tarski(X2,X0)
% 2.80/0.97      | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2
% 2.80/0.97      | sK4 != X1 ),
% 2.80/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_486,plain,
% 2.80/0.97      ( ~ v2_tex_2(X0,sK4)
% 2.80/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.97      | ~ r1_tarski(X1,X0)
% 2.80/0.97      | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1 ),
% 2.80/0.97      inference(unflattening,[status(thm)],[c_485]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2861,plain,
% 2.80/0.97      ( k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
% 2.80/0.97      | v2_tex_2(X0,sK4) != iProver_top
% 2.80/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3146,plain,
% 2.80/0.97      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 2.80/0.97      | v2_tex_2(sK5,sK4) != iProver_top
% 2.80/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.97      | r1_tarski(X0,sK5) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_2864,c_2861]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_27,plain,
% 2.80/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_23,negated_conjecture,
% 2.80/0.97      ( v2_tex_2(sK5,sK4) ),
% 2.80/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_774,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.97      | ~ r1_tarski(X1,X0)
% 2.80/0.97      | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
% 2.80/0.97      | sK5 != X0
% 2.80/0.97      | sK4 != sK4 ),
% 2.80/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_486]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_775,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ r1_tarski(X0,sK5)
% 2.80/0.98      | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0 ),
% 2.80/0.98      inference(unflattening,[status(thm)],[c_774]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_776,plain,
% 2.80/0.98      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 2.80/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.98      | r1_tarski(X0,sK5) != iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3802,plain,
% 2.80/0.98      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 2.80/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.98      | r1_tarski(X0,sK5) != iProver_top ),
% 2.80/0.98      inference(global_propositional_subsumption,
% 2.80/0.98                [status(thm)],
% 2.80/0.98                [c_3146,c_27,c_776]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_4122,plain,
% 2.80/0.98      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 2.80/0.98      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK5) != iProver_top
% 2.80/0.98      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.80/0.98      inference(superposition,[status(thm)],[c_2869,c_3802]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_6002,plain,
% 2.80/0.98      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 2.80/0.98      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 2.80/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 2.80/0.98      inference(superposition,[status(thm)],[c_4124,c_4122]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3281,plain,
% 2.80/0.98      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 2.80/0.98      inference(superposition,[status(thm)],[c_2864,c_2857]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_6,plain,
% 2.80/0.98      ( ~ r1_tarski(X0,X1)
% 2.80/0.98      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 2.80/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_2874,plain,
% 2.80/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 2.80/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3567,plain,
% 2.80/0.98      ( k1_setfam_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,u1_struct_0(sK4))) = sK5 ),
% 2.80/0.98      inference(superposition,[status(thm)],[c_3281,c_2874]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_4,plain,
% 2.80/0.98      ( r2_hidden(X0,X1)
% 2.80/0.98      | ~ r2_hidden(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.80/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_2876,plain,
% 2.80/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.80/0.98      | r2_hidden(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_4230,plain,
% 2.80/0.98      ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 2.80/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 2.80/0.98      inference(superposition,[status(thm)],[c_3567,c_2876]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_8411,plain,
% 2.80/0.98      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 2.80/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 2.80/0.98      inference(global_propositional_subsumption,
% 2.80/0.98                [status(thm)],
% 2.80/0.98                [c_6002,c_4230]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_8425,plain,
% 2.80/0.98      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 2.80/0.98      inference(superposition,[status(thm)],[c_2867,c_8411]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_20,negated_conjecture,
% 2.80/0.98      ( ~ v4_pre_topc(X0,sK4)
% 2.80/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0) ),
% 2.80/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_2868,plain,
% 2.80/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0)
% 2.80/0.98      | v4_pre_topc(X0,sK4) != iProver_top
% 2.80/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_8637,plain,
% 2.80/0.98      ( v4_pre_topc(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK4) != iProver_top
% 2.80/0.98      | m1_subset_1(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.80/0.98      inference(superposition,[status(thm)],[c_8425,c_2868]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_4486,plain,
% 2.80/0.98      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_4489,plain,
% 2.80/0.98      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.80/0.98      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_4486]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_4491,plain,
% 2.80/0.98      ( m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.80/0.98      | r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_4489]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_4243,plain,
% 2.80/0.98      ( r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
% 2.80/0.98      | r2_hidden(sK6,sK5) != iProver_top ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_4230]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_19,plain,
% 2.80/0.98      ( ~ v2_tex_2(X0,X1)
% 2.80/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.98      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.98      | ~ r1_tarski(X2,X0)
% 2.80/0.98      | ~ l1_pre_topc(X1) ),
% 2.80/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_464,plain,
% 2.80/0.98      ( ~ v2_tex_2(X0,X1)
% 2.80/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.98      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/0.98      | ~ r1_tarski(X2,X0)
% 2.80/0.98      | sK4 != X1 ),
% 2.80/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_465,plain,
% 2.80/0.98      ( ~ v2_tex_2(X0,sK4)
% 2.80/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ r1_tarski(X1,X0) ),
% 2.80/0.98      inference(unflattening,[status(thm)],[c_464]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3071,plain,
% 2.80/0.98      ( ~ v2_tex_2(sK5,sK4)
% 2.80/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | m1_subset_1(sK3(sK4,sK5,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ r1_tarski(X0,sK5) ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_465]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3322,plain,
% 2.80/0.98      ( ~ v2_tex_2(sK5,sK4)
% 2.80/0.98      | ~ m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | m1_subset_1(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_3071]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3326,plain,
% 2.80/0.98      ( v2_tex_2(sK5,sK4) != iProver_top
% 2.80/0.98      | m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.98      | m1_subset_1(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.80/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.98      | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) != iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_3322]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_18,plain,
% 2.80/0.98      ( v4_pre_topc(sK3(X0,X1,X2),X0)
% 2.80/0.98      | ~ v2_tex_2(X1,X0)
% 2.80/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.80/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.80/0.98      | ~ r1_tarski(X2,X1)
% 2.80/0.98      | ~ l1_pre_topc(X0) ),
% 2.80/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_443,plain,
% 2.80/0.98      ( v4_pre_topc(sK3(X0,X1,X2),X0)
% 2.80/0.98      | ~ v2_tex_2(X1,X0)
% 2.80/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.80/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.80/0.98      | ~ r1_tarski(X2,X1)
% 2.80/0.98      | sK4 != X0 ),
% 2.80/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_444,plain,
% 2.80/0.98      ( v4_pre_topc(sK3(sK4,X0,X1),sK4)
% 2.80/0.98      | ~ v2_tex_2(X0,sK4)
% 2.80/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ r1_tarski(X1,X0) ),
% 2.80/0.98      inference(unflattening,[status(thm)],[c_443]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3068,plain,
% 2.80/0.98      ( v4_pre_topc(sK3(sK4,sK5,X0),sK4)
% 2.80/0.98      | ~ v2_tex_2(sK5,sK4)
% 2.80/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ r1_tarski(X0,sK5) ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_444]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3323,plain,
% 2.80/0.98      ( v4_pre_topc(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK4)
% 2.80/0.98      | ~ v2_tex_2(sK5,sK4)
% 2.80/0.98      | ~ m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.80/0.98      | ~ r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_3068]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3324,plain,
% 2.80/0.98      ( v4_pre_topc(sK3(sK4,sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)),sK4) = iProver_top
% 2.80/0.98      | v2_tex_2(sK5,sK4) != iProver_top
% 2.80/0.98      | m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.80/0.98      | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) != iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_3323]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3153,plain,
% 2.80/0.98      ( ~ m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(sK5))
% 2.80/0.98      | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_1411]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3154,plain,
% 2.80/0.98      ( m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(sK5)) != iProver_top
% 2.80/0.98      | r1_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),sK5) = iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_3153]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3118,plain,
% 2.80/0.98      ( m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(sK5))
% 2.80/0.98      | ~ r2_hidden(sK6,sK5) ),
% 2.80/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_3119,plain,
% 2.80/0.98      ( m1_subset_1(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6),k1_zfmisc_1(sK5)) = iProver_top
% 2.80/0.98      | r2_hidden(sK6,sK5) != iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_3118]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_30,plain,
% 2.80/0.98      ( r2_hidden(sK6,sK5) = iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(c_28,plain,
% 2.80/0.98      ( v2_tex_2(sK5,sK4) = iProver_top ),
% 2.80/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.80/0.98  
% 2.80/0.98  cnf(contradiction,plain,
% 2.80/0.98      ( $false ),
% 2.80/0.98      inference(minisat,
% 2.80/0.98                [status(thm)],
% 2.80/0.98                [c_8637,c_4491,c_4243,c_3326,c_3324,c_3154,c_3119,c_30,
% 2.80/0.98                 c_28,c_27]) ).
% 2.80/0.98  
% 2.80/0.98  
% 2.80/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/0.98  
% 2.80/0.98  ------                               Statistics
% 2.80/0.98  
% 2.80/0.98  ------ General
% 2.80/0.98  
% 2.80/0.98  abstr_ref_over_cycles:                  0
% 2.80/0.98  abstr_ref_under_cycles:                 0
% 2.80/0.98  gc_basic_clause_elim:                   0
% 2.80/0.98  forced_gc_time:                         0
% 2.80/0.98  parsing_time:                           0.01
% 2.80/0.98  unif_index_cands_time:                  0.
% 2.80/0.98  unif_index_add_time:                    0.
% 2.80/0.98  orderings_time:                         0.
% 2.80/0.98  out_proof_time:                         0.008
% 2.80/0.98  total_time:                             0.272
% 2.80/0.98  num_of_symbols:                         50
% 2.80/0.98  num_of_terms:                           7605
% 2.80/0.98  
% 2.80/0.98  ------ Preprocessing
% 2.80/0.98  
% 2.80/0.98  num_of_splits:                          0
% 2.80/0.98  num_of_split_atoms:                     0
% 2.80/0.98  num_of_reused_defs:                     0
% 2.80/0.98  num_eq_ax_congr_red:                    29
% 2.80/0.98  num_of_sem_filtered_clauses:            1
% 2.80/0.98  num_of_subtypes:                        0
% 2.80/0.98  monotx_restored_types:                  0
% 2.80/0.98  sat_num_of_epr_types:                   0
% 2.80/0.98  sat_num_of_non_cyclic_types:            0
% 2.80/0.98  sat_guarded_non_collapsed_types:        0
% 2.80/0.98  num_pure_diseq_elim:                    0
% 2.80/0.98  simp_replaced_by:                       0
% 2.80/0.98  res_preprocessed:                       127
% 2.80/0.98  prep_upred:                             0
% 2.80/0.98  prep_unflattend:                        93
% 2.80/0.98  smt_new_axioms:                         0
% 2.80/0.98  pred_elim_cands:                        5
% 2.80/0.98  pred_elim:                              2
% 2.80/0.98  pred_elim_cl:                           2
% 2.80/0.98  pred_elim_cycles:                       9
% 2.80/0.98  merged_defs:                            8
% 2.80/0.98  merged_defs_ncl:                        0
% 2.80/0.98  bin_hyper_res:                          9
% 2.80/0.98  prep_cycles:                            4
% 2.80/0.98  pred_elim_time:                         0.034
% 2.80/0.98  splitting_time:                         0.
% 2.80/0.98  sem_filter_time:                        0.
% 2.80/0.98  monotx_time:                            0.001
% 2.80/0.98  subtype_inf_time:                       0.
% 2.80/0.98  
% 2.80/0.98  ------ Problem properties
% 2.80/0.98  
% 2.80/0.98  clauses:                                24
% 2.80/0.98  conjectures:                            5
% 2.80/0.98  epr:                                    2
% 2.80/0.98  horn:                                   19
% 2.80/0.98  ground:                                 4
% 2.80/0.98  unary:                                  4
% 2.80/0.98  binary:                                 7
% 2.80/0.98  lits:                                   66
% 2.80/0.98  lits_eq:                                9
% 2.80/0.98  fd_pure:                                0
% 2.80/0.98  fd_pseudo:                              0
% 2.80/0.98  fd_cond:                                0
% 2.80/0.98  fd_pseudo_cond:                         5
% 2.80/0.98  ac_symbols:                             0
% 2.80/0.98  
% 2.80/0.98  ------ Propositional Solver
% 2.80/0.98  
% 2.80/0.98  prop_solver_calls:                      27
% 2.80/0.98  prop_fast_solver_calls:                 1374
% 2.80/0.98  smt_solver_calls:                       0
% 2.80/0.98  smt_fast_solver_calls:                  0
% 2.80/0.98  prop_num_of_clauses:                    2798
% 2.80/0.98  prop_preprocess_simplified:             8662
% 2.80/0.98  prop_fo_subsumed:                       13
% 2.80/0.98  prop_solver_time:                       0.
% 2.80/0.98  smt_solver_time:                        0.
% 2.80/0.98  smt_fast_solver_time:                   0.
% 2.80/0.98  prop_fast_solver_time:                  0.
% 2.80/0.98  prop_unsat_core_time:                   0.
% 2.80/0.98  
% 2.80/0.98  ------ QBF
% 2.80/0.98  
% 2.80/0.98  qbf_q_res:                              0
% 2.80/0.98  qbf_num_tautologies:                    0
% 2.80/0.98  qbf_prep_cycles:                        0
% 2.80/0.98  
% 2.80/0.98  ------ BMC1
% 2.80/0.98  
% 2.80/0.98  bmc1_current_bound:                     -1
% 2.80/0.98  bmc1_last_solved_bound:                 -1
% 2.80/0.98  bmc1_unsat_core_size:                   -1
% 2.80/0.98  bmc1_unsat_core_parents_size:           -1
% 2.80/0.98  bmc1_merge_next_fun:                    0
% 2.80/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.80/0.98  
% 2.80/0.98  ------ Instantiation
% 2.80/0.98  
% 2.80/0.98  inst_num_of_clauses:                    739
% 2.80/0.98  inst_num_in_passive:                    415
% 2.80/0.98  inst_num_in_active:                     253
% 2.80/0.98  inst_num_in_unprocessed:                71
% 2.80/0.98  inst_num_of_loops:                      350
% 2.80/0.98  inst_num_of_learning_restarts:          0
% 2.80/0.98  inst_num_moves_active_passive:          95
% 2.80/0.98  inst_lit_activity:                      0
% 2.80/0.98  inst_lit_activity_moves:                0
% 2.80/0.98  inst_num_tautologies:                   0
% 2.80/0.98  inst_num_prop_implied:                  0
% 2.80/0.98  inst_num_existing_simplified:           0
% 2.80/0.98  inst_num_eq_res_simplified:             0
% 2.80/0.98  inst_num_child_elim:                    0
% 2.80/0.98  inst_num_of_dismatching_blockings:      249
% 2.80/0.98  inst_num_of_non_proper_insts:           490
% 2.80/0.98  inst_num_of_duplicates:                 0
% 2.80/0.98  inst_inst_num_from_inst_to_res:         0
% 2.80/0.98  inst_dismatching_checking_time:         0.
% 2.80/0.98  
% 2.80/0.98  ------ Resolution
% 2.80/0.98  
% 2.80/0.98  res_num_of_clauses:                     0
% 2.80/0.98  res_num_in_passive:                     0
% 2.80/0.98  res_num_in_active:                      0
% 2.80/0.98  res_num_of_loops:                       131
% 2.80/0.98  res_forward_subset_subsumed:            29
% 2.80/0.98  res_backward_subset_subsumed:           0
% 2.80/0.98  res_forward_subsumed:                   0
% 2.80/0.98  res_backward_subsumed:                  0
% 2.80/0.98  res_forward_subsumption_resolution:     2
% 2.80/0.98  res_backward_subsumption_resolution:    0
% 2.80/0.98  res_clause_to_clause_subsumption:       896
% 2.80/0.98  res_orphan_elimination:                 0
% 2.80/0.98  res_tautology_del:                      44
% 2.80/0.98  res_num_eq_res_simplified:              0
% 2.80/0.98  res_num_sel_changes:                    0
% 2.80/0.98  res_moves_from_active_to_pass:          0
% 2.80/0.98  
% 2.80/0.98  ------ Superposition
% 2.80/0.98  
% 2.80/0.98  sup_time_total:                         0.
% 2.80/0.98  sup_time_generating:                    0.
% 2.80/0.98  sup_time_sim_full:                      0.
% 2.80/0.98  sup_time_sim_immed:                     0.
% 2.80/0.98  
% 2.80/0.98  sup_num_of_clauses:                     133
% 2.80/0.98  sup_num_in_active:                      69
% 2.80/0.98  sup_num_in_passive:                     64
% 2.80/0.98  sup_num_of_loops:                       68
% 2.80/0.98  sup_fw_superposition:                   55
% 2.80/0.98  sup_bw_superposition:                   70
% 2.80/0.98  sup_immediate_simplified:               10
% 2.80/0.98  sup_given_eliminated:                   0
% 2.80/0.98  comparisons_done:                       0
% 2.80/0.98  comparisons_avoided:                    2
% 2.80/0.98  
% 2.80/0.98  ------ Simplifications
% 2.80/0.98  
% 2.80/0.98  
% 2.80/0.98  sim_fw_subset_subsumed:                 4
% 2.80/0.98  sim_bw_subset_subsumed:                 1
% 2.80/0.98  sim_fw_subsumed:                        4
% 2.80/0.98  sim_bw_subsumed:                        0
% 2.80/0.98  sim_fw_subsumption_res:                 3
% 2.80/0.98  sim_bw_subsumption_res:                 0
% 2.80/0.98  sim_tautology_del:                      10
% 2.80/0.98  sim_eq_tautology_del:                   2
% 2.80/0.98  sim_eq_res_simp:                        4
% 2.80/0.98  sim_fw_demodulated:                     0
% 2.80/0.98  sim_bw_demodulated:                     0
% 2.80/0.98  sim_light_normalised:                   0
% 2.80/0.98  sim_joinable_taut:                      0
% 2.80/0.98  sim_joinable_simp:                      0
% 2.80/0.98  sim_ac_normalised:                      0
% 2.80/0.98  sim_smt_subsumption:                    0
% 2.80/0.98  
%------------------------------------------------------------------------------

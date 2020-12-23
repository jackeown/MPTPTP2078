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
% DateTime   : Thu Dec  3 12:16:22 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 329 expanded)
%              Number of clauses        :   57 (  83 expanded)
%              Number of leaves         :   14 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  440 (1780 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & v1_tops_2(X1,X0) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & v1_tops_2(X1,X0) )
                 => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X2,X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK5),X0)
        & v1_tops_2(sK5,X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK4,X2),X0)
            & v1_tops_2(X2,X0)
            & v1_tops_2(sK4,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X2,X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X1,X2),sK3)
              & v1_tops_2(X2,sK3)
              & v1_tops_2(X1,sK3)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    & v1_tops_2(sK5,sK3)
    & v1_tops_2(sK4,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f31,f30,f29])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    v1_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v1_tops_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2471,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1)
    | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0)
    | r1_tarski(k2_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_8,c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1445,plain,
    ( r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_11,c_20])).

cnf(c_2339,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_2,c_1445])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2650,plain,
    ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),sK4)
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_2339,c_0])).

cnf(c_7303,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))),X0)
    | r1_tarski(k2_xboole_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_2471,c_2650])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1443,plain,
    ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_11,c_19])).

cnf(c_2335,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_2,c_1443])).

cnf(c_2638,plain,
    ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),sK5)
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_2335,c_0])).

cnf(c_8144,plain,
    ( r1_tarski(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_7303,c_2638])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_358,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_359,plain,
    ( v1_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | r2_hidden(sK2(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_1558,plain,
    ( v1_tops_2(X0,sK3)
    | r2_hidden(sK2(sK3,X0),X0)
    | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_10,c_359])).

cnf(c_2477,plain,
    ( v1_tops_2(k2_xboole_0(X0,X1),sK3)
    | r2_hidden(sK2(sK3,k2_xboole_0(X0,X1)),X1)
    | r2_hidden(sK2(sK3,k2_xboole_0(X0,X1)),X0)
    | ~ r1_tarski(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_8,c_1558])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_292,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X4,X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | sK2(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_293,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(sK2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_14,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_309,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_293,c_14])).

cnf(c_324,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_309,c_21])).

cnf(c_325,plain,
    ( ~ v1_tops_2(X0,sK3)
    | v1_tops_2(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK3,X1),X0) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1750,plain,
    ( v1_tops_2(X0,sK3)
    | ~ v1_tops_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK3,X0),sK4) ),
    inference(resolution,[status(thm)],[c_325,c_20])).

cnf(c_18,negated_conjecture,
    ( v1_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1835,plain,
    ( v1_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK3,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1750,c_18])).

cnf(c_1950,plain,
    ( v1_tops_2(X0,sK3)
    | ~ r2_hidden(sK2(sK3,X0),sK4)
    | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_1835,c_10])).

cnf(c_4815,plain,
    ( v1_tops_2(k2_xboole_0(sK4,X0),sK3)
    | r2_hidden(sK2(sK3,k2_xboole_0(sK4,X0)),X0)
    | ~ r1_tarski(k2_xboole_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_2477,c_1950])).

cnf(c_1746,plain,
    ( v1_tops_2(X0,sK3)
    | ~ v1_tops_2(sK5,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK3,X0),sK5) ),
    inference(resolution,[status(thm)],[c_325,c_19])).

cnf(c_17,negated_conjecture,
    ( v1_tops_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1806,plain,
    ( v1_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK3,X0),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1746,c_17])).

cnf(c_1828,plain,
    ( v1_tops_2(X0,sK3)
    | ~ r2_hidden(sK2(sK3,X0),sK5)
    | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_1806,c_10])).

cnf(c_5132,plain,
    ( v1_tops_2(k2_xboole_0(sK4,sK5),sK3)
    | ~ r1_tarski(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_4815,c_1828])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_166,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_167,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_166])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_167])).

cnf(c_578,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_579,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_578])).

cnf(c_617,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_210,c_579])).

cnf(c_1647,plain,
    ( ~ r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) = k2_xboole_0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_697,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1630,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_1646,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    | ~ v1_tops_2(k2_xboole_0(sK4,sK5),X0)
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != k2_xboole_0(sK4,sK5)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_1649,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    | ~ v1_tops_2(k2_xboole_0(sK4,sK5),sK3)
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != k2_xboole_0(sK4,sK5)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1646])).

cnf(c_691,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_708,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_16,negated_conjecture,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8144,c_5132,c_1647,c_1649,c_1445,c_1443,c_708,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n016.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:04:19 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.65/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/0.96  
% 3.65/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.96  
% 3.65/0.96  ------  iProver source info
% 3.65/0.96  
% 3.65/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.96  git: non_committed_changes: false
% 3.65/0.96  git: last_make_outside_of_git: false
% 3.65/0.96  
% 3.65/0.96  ------ 
% 3.65/0.96  ------ Parsing...
% 3.65/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.96  
% 3.65/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.65/0.96  
% 3.65/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.96  
% 3.65/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.96  ------ Proving...
% 3.65/0.96  ------ Problem Properties 
% 3.65/0.96  
% 3.65/0.96  
% 3.65/0.96  clauses                                 20
% 3.65/0.96  conjectures                             5
% 3.65/0.96  EPR                                     3
% 3.65/0.96  Horn                                    15
% 3.65/0.96  unary                                   5
% 3.65/0.96  binary                                  6
% 3.65/0.96  lits                                    47
% 3.65/0.96  lits eq                                 4
% 3.65/0.96  fd_pure                                 0
% 3.65/0.96  fd_pseudo                               0
% 3.65/0.96  fd_cond                                 0
% 3.65/0.96  fd_pseudo_cond                          3
% 3.65/0.96  AC symbols                              0
% 3.65/0.96  
% 3.65/0.96  ------ Input Options Time Limit: Unbounded
% 3.65/0.96  
% 3.65/0.96  
% 3.65/0.96  ------ 
% 3.65/0.96  Current options:
% 3.65/0.96  ------ 
% 3.65/0.96  
% 3.65/0.96  
% 3.65/0.96  
% 3.65/0.96  
% 3.65/0.96  ------ Proving...
% 3.65/0.96  
% 3.65/0.96  
% 3.65/0.96  % SZS status Theorem for theBenchmark.p
% 3.65/0.96  
% 3.65/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.96  
% 3.65/0.96  fof(f2,axiom,(
% 3.65/0.96    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.65/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.96  
% 3.65/0.96  fof(f19,plain,(
% 3.65/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.65/0.96    inference(nnf_transformation,[],[f2])).
% 3.65/0.96  
% 3.65/0.96  fof(f20,plain,(
% 3.65/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.65/0.96    inference(flattening,[],[f19])).
% 3.65/0.96  
% 3.65/0.96  fof(f21,plain,(
% 3.65/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.65/0.96    inference(rectify,[],[f20])).
% 3.65/0.96  
% 3.65/0.96  fof(f22,plain,(
% 3.65/0.96    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.65/0.96    introduced(choice_axiom,[])).
% 3.65/0.96  
% 3.65/0.96  fof(f23,plain,(
% 3.65/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.65/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 3.65/0.96  
% 3.65/0.96  fof(f36,plain,(
% 3.65/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.65/0.96    inference(cnf_transformation,[],[f23])).
% 3.65/0.96  
% 3.65/0.96  fof(f57,plain,(
% 3.65/0.96    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.65/0.96    inference(equality_resolution,[],[f36])).
% 3.65/0.96  
% 3.65/0.96  fof(f1,axiom,(
% 3.65/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.65/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.96  
% 3.65/0.96  fof(f8,plain,(
% 3.65/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.65/0.96    inference(ennf_transformation,[],[f1])).
% 3.65/0.96  
% 3.65/0.96  fof(f15,plain,(
% 3.65/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.65/0.96    inference(nnf_transformation,[],[f8])).
% 3.65/0.96  
% 3.65/0.96  fof(f16,plain,(
% 3.65/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.65/0.96    inference(rectify,[],[f15])).
% 3.65/0.96  
% 3.65/0.96  fof(f17,plain,(
% 3.65/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.65/0.96    introduced(choice_axiom,[])).
% 3.65/0.96  
% 3.65/0.96  fof(f18,plain,(
% 3.65/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.65/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 3.65/0.96  
% 3.65/0.96  fof(f34,plain,(
% 3.65/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.65/0.96    inference(cnf_transformation,[],[f18])).
% 3.65/0.96  
% 3.65/0.96  fof(f33,plain,(
% 3.65/0.96    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.65/0.96    inference(cnf_transformation,[],[f18])).
% 3.65/0.96  
% 3.65/0.96  fof(f4,axiom,(
% 3.65/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.65/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.96  
% 3.65/0.96  fof(f24,plain,(
% 3.65/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.65/0.96    inference(nnf_transformation,[],[f4])).
% 3.65/0.96  
% 3.65/0.96  fof(f43,plain,(
% 3.65/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.65/0.96    inference(cnf_transformation,[],[f24])).
% 3.65/0.96  
% 3.65/0.96  fof(f6,conjecture,(
% 3.65/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.65/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.96  
% 3.65/0.96  fof(f7,negated_conjecture,(
% 3.65/0.96    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.65/0.96    inference(negated_conjecture,[],[f6])).
% 3.65/0.96  
% 3.65/0.96  fof(f13,plain,(
% 3.65/0.96    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v1_tops_2(X2,X0) & v1_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.65/0.96    inference(ennf_transformation,[],[f7])).
% 3.65/0.96  
% 3.65/0.96  fof(f14,plain,(
% 3.65/0.96    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.65/0.96    inference(flattening,[],[f13])).
% 3.65/0.96  
% 3.65/0.96  fof(f31,plain,(
% 3.65/0.96    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK5),X0) & v1_tops_2(sK5,X0) & v1_tops_2(X1,X0) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.65/0.96    introduced(choice_axiom,[])).
% 3.65/0.96  
% 3.65/0.96  fof(f30,plain,(
% 3.65/0.96    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK4,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(sK4,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.65/0.96    introduced(choice_axiom,[])).
% 3.65/0.96  
% 3.65/0.96  fof(f29,plain,(
% 3.65/0.96    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X1,X2),sK3) & v1_tops_2(X2,sK3) & v1_tops_2(X1,sK3) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3))),
% 3.65/0.96    introduced(choice_axiom,[])).
% 3.65/0.96  
% 3.65/0.96  fof(f32,plain,(
% 3.65/0.96    ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) & v1_tops_2(sK5,sK3) & v1_tops_2(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3)),
% 3.65/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f31,f30,f29])).
% 3.65/0.96  
% 3.65/0.96  fof(f50,plain,(
% 3.65/0.96    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 3.65/0.96    inference(cnf_transformation,[],[f32])).
% 3.65/0.96  
% 3.65/0.96  fof(f35,plain,(
% 3.65/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.65/0.96    inference(cnf_transformation,[],[f18])).
% 3.65/0.96  
% 3.65/0.96  fof(f51,plain,(
% 3.65/0.96    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 3.65/0.96    inference(cnf_transformation,[],[f32])).
% 3.65/0.96  
% 3.65/0.96  fof(f44,plain,(
% 3.65/0.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.65/0.96    inference(cnf_transformation,[],[f24])).
% 3.65/0.96  
% 3.65/0.96  fof(f5,axiom,(
% 3.65/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 3.65/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.96  
% 3.65/0.96  fof(f11,plain,(
% 3.65/0.96    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.65/0.96    inference(ennf_transformation,[],[f5])).
% 3.65/0.96  
% 3.65/0.96  fof(f12,plain,(
% 3.65/0.96    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.65/0.96    inference(flattening,[],[f11])).
% 3.65/0.96  
% 3.65/0.96  fof(f25,plain,(
% 3.65/0.96    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.65/0.96    inference(nnf_transformation,[],[f12])).
% 3.65/0.96  
% 3.65/0.96  fof(f26,plain,(
% 3.65/0.96    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.65/0.96    inference(rectify,[],[f25])).
% 3.65/0.96  
% 3.65/0.96  fof(f27,plain,(
% 3.65/0.96    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.65/0.96    introduced(choice_axiom,[])).
% 3.65/0.96  
% 3.65/0.96  fof(f28,plain,(
% 3.65/0.96    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.65/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 3.65/0.96  
% 3.65/0.96  fof(f47,plain,(
% 3.65/0.96    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.65/0.96    inference(cnf_transformation,[],[f28])).
% 3.65/0.96  
% 3.65/0.96  fof(f49,plain,(
% 3.65/0.96    l1_pre_topc(sK3)),
% 3.65/0.96    inference(cnf_transformation,[],[f32])).
% 3.65/0.96  
% 3.65/0.96  fof(f48,plain,(
% 3.65/0.96    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.65/0.96    inference(cnf_transformation,[],[f28])).
% 3.65/0.96  
% 3.65/0.96  fof(f45,plain,(
% 3.65/0.96    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.65/0.96    inference(cnf_transformation,[],[f28])).
% 3.65/0.96  
% 3.65/0.96  fof(f46,plain,(
% 3.65/0.96    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.65/0.96    inference(cnf_transformation,[],[f28])).
% 3.65/0.96  
% 3.65/0.96  fof(f52,plain,(
% 3.65/0.96    v1_tops_2(sK4,sK3)),
% 3.65/0.96    inference(cnf_transformation,[],[f32])).
% 3.65/0.96  
% 3.65/0.96  fof(f53,plain,(
% 3.65/0.96    v1_tops_2(sK5,sK3)),
% 3.65/0.96    inference(cnf_transformation,[],[f32])).
% 3.65/0.96  
% 3.65/0.96  fof(f3,axiom,(
% 3.65/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.65/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.96  
% 3.65/0.96  fof(f9,plain,(
% 3.65/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.65/0.96    inference(ennf_transformation,[],[f3])).
% 3.65/0.96  
% 3.65/0.96  fof(f10,plain,(
% 3.65/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/0.96    inference(flattening,[],[f9])).
% 3.65/0.96  
% 3.65/0.96  fof(f42,plain,(
% 3.65/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.65/0.96    inference(cnf_transformation,[],[f10])).
% 3.65/0.96  
% 3.65/0.96  fof(f54,plain,(
% 3.65/0.96    ~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)),
% 3.65/0.96    inference(cnf_transformation,[],[f32])).
% 3.65/0.96  
% 3.65/0.96  cnf(c_8,plain,
% 3.65/0.96      ( r2_hidden(X0,X1)
% 3.65/0.96      | r2_hidden(X0,X2)
% 3.65/0.96      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.65/0.96      inference(cnf_transformation,[],[f57]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1,plain,
% 3.65/0.96      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.65/0.96      inference(cnf_transformation,[],[f34]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_2471,plain,
% 3.65/0.96      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1)
% 3.65/0.96      | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0)
% 3.65/0.96      | r1_tarski(k2_xboole_0(X0,X1),X2) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_8,c_1]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_2,plain,
% 3.65/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.65/0.96      inference(cnf_transformation,[],[f33]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_11,plain,
% 3.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.65/0.96      inference(cnf_transformation,[],[f43]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_20,negated_conjecture,
% 3.65/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 3.65/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1445,plain,
% 3.65/0.96      ( r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_11,c_20]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_2339,plain,
% 3.65/0.96      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.96      | ~ r2_hidden(X0,sK4) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_2,c_1445]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_0,plain,
% 3.65/0.96      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.65/0.96      inference(cnf_transformation,[],[f35]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_2650,plain,
% 3.65/0.96      ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),sK4)
% 3.65/0.96      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_2339,c_0]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_7303,plain,
% 3.65/0.96      ( r2_hidden(sK0(k2_xboole_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))),X0)
% 3.65/0.96      | r1_tarski(k2_xboole_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_2471,c_2650]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_19,negated_conjecture,
% 3.65/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 3.65/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1443,plain,
% 3.65/0.96      ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_11,c_19]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_2335,plain,
% 3.65/0.96      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.96      | ~ r2_hidden(X0,sK5) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_2,c_1443]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_2638,plain,
% 3.65/0.96      ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),sK5)
% 3.65/0.96      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_2335,c_0]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_8144,plain,
% 3.65/0.96      ( r1_tarski(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_7303,c_2638]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_10,plain,
% 3.65/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.65/0.96      inference(cnf_transformation,[],[f44]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_13,plain,
% 3.65/0.96      ( v1_tops_2(X0,X1)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | r2_hidden(sK2(X1,X0),X0)
% 3.65/0.96      | ~ l1_pre_topc(X1) ),
% 3.65/0.96      inference(cnf_transformation,[],[f47]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_21,negated_conjecture,
% 3.65/0.96      ( l1_pre_topc(sK3) ),
% 3.65/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_358,plain,
% 3.65/0.96      ( v1_tops_2(X0,X1)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | r2_hidden(sK2(X1,X0),X0)
% 3.65/0.96      | sK3 != X1 ),
% 3.65/0.96      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_359,plain,
% 3.65/0.96      ( v1_tops_2(X0,sK3)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.65/0.96      | r2_hidden(sK2(sK3,X0),X0) ),
% 3.65/0.96      inference(unflattening,[status(thm)],[c_358]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1558,plain,
% 3.65/0.96      ( v1_tops_2(X0,sK3)
% 3.65/0.96      | r2_hidden(sK2(sK3,X0),X0)
% 3.65/0.96      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_10,c_359]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_2477,plain,
% 3.65/0.96      ( v1_tops_2(k2_xboole_0(X0,X1),sK3)
% 3.65/0.96      | r2_hidden(sK2(sK3,k2_xboole_0(X0,X1)),X1)
% 3.65/0.96      | r2_hidden(sK2(sK3,k2_xboole_0(X0,X1)),X0)
% 3.65/0.96      | ~ r1_tarski(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_8,c_1558]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_12,plain,
% 3.65/0.96      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 3.65/0.96      | v1_tops_2(X1,X0)
% 3.65/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.65/0.96      | ~ l1_pre_topc(X0) ),
% 3.65/0.96      inference(cnf_transformation,[],[f48]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_15,plain,
% 3.65/0.96      ( v3_pre_topc(X0,X1)
% 3.65/0.96      | ~ v1_tops_2(X2,X1)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | ~ r2_hidden(X0,X2)
% 3.65/0.96      | ~ l1_pre_topc(X1) ),
% 3.65/0.96      inference(cnf_transformation,[],[f45]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_292,plain,
% 3.65/0.96      ( ~ v1_tops_2(X0,X1)
% 3.65/0.96      | v1_tops_2(X2,X3)
% 3.65/0.96      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | ~ r2_hidden(X4,X0)
% 3.65/0.96      | ~ l1_pre_topc(X3)
% 3.65/0.96      | ~ l1_pre_topc(X1)
% 3.65/0.96      | X1 != X3
% 3.65/0.96      | sK2(X3,X2) != X4 ),
% 3.65/0.96      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_293,plain,
% 3.65/0.96      ( ~ v1_tops_2(X0,X1)
% 3.65/0.96      | v1_tops_2(X2,X1)
% 3.65/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | ~ m1_subset_1(sK2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.96      | ~ r2_hidden(sK2(X1,X2),X0)
% 3.65/0.96      | ~ l1_pre_topc(X1) ),
% 3.65/0.96      inference(unflattening,[status(thm)],[c_292]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_14,plain,
% 3.65/0.96      ( v1_tops_2(X0,X1)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.96      | ~ l1_pre_topc(X1) ),
% 3.65/0.96      inference(cnf_transformation,[],[f46]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_309,plain,
% 3.65/0.96      ( ~ v1_tops_2(X0,X1)
% 3.65/0.96      | v1_tops_2(X2,X1)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | ~ r2_hidden(sK2(X1,X2),X0)
% 3.65/0.96      | ~ l1_pre_topc(X1) ),
% 3.65/0.96      inference(forward_subsumption_resolution,
% 3.65/0.96                [status(thm)],
% 3.65/0.96                [c_293,c_14]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_324,plain,
% 3.65/0.96      ( ~ v1_tops_2(X0,X1)
% 3.65/0.96      | v1_tops_2(X2,X1)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.65/0.96      | ~ r2_hidden(sK2(X1,X2),X0)
% 3.65/0.96      | sK3 != X1 ),
% 3.65/0.96      inference(resolution_lifted,[status(thm)],[c_309,c_21]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_325,plain,
% 3.65/0.96      ( ~ v1_tops_2(X0,sK3)
% 3.65/0.96      | v1_tops_2(X1,sK3)
% 3.65/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.65/0.96      | ~ r2_hidden(sK2(sK3,X1),X0) ),
% 3.65/0.96      inference(unflattening,[status(thm)],[c_324]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1750,plain,
% 3.65/0.96      ( v1_tops_2(X0,sK3)
% 3.65/0.96      | ~ v1_tops_2(sK4,sK3)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.65/0.96      | ~ r2_hidden(sK2(sK3,X0),sK4) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_325,c_20]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_18,negated_conjecture,
% 3.65/0.96      ( v1_tops_2(sK4,sK3) ),
% 3.65/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1835,plain,
% 3.65/0.96      ( v1_tops_2(X0,sK3)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.65/0.96      | ~ r2_hidden(sK2(sK3,X0),sK4) ),
% 3.65/0.96      inference(global_propositional_subsumption,
% 3.65/0.96                [status(thm)],
% 3.65/0.96                [c_1750,c_18]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1950,plain,
% 3.65/0.96      ( v1_tops_2(X0,sK3)
% 3.65/0.96      | ~ r2_hidden(sK2(sK3,X0),sK4)
% 3.65/0.96      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_1835,c_10]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_4815,plain,
% 3.65/0.96      ( v1_tops_2(k2_xboole_0(sK4,X0),sK3)
% 3.65/0.96      | r2_hidden(sK2(sK3,k2_xboole_0(sK4,X0)),X0)
% 3.65/0.96      | ~ r1_tarski(k2_xboole_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_2477,c_1950]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1746,plain,
% 3.65/0.96      ( v1_tops_2(X0,sK3)
% 3.65/0.96      | ~ v1_tops_2(sK5,sK3)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.65/0.96      | ~ r2_hidden(sK2(sK3,X0),sK5) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_325,c_19]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_17,negated_conjecture,
% 3.65/0.96      ( v1_tops_2(sK5,sK3) ),
% 3.65/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1806,plain,
% 3.65/0.96      ( v1_tops_2(X0,sK3)
% 3.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.65/0.96      | ~ r2_hidden(sK2(sK3,X0),sK5) ),
% 3.65/0.96      inference(global_propositional_subsumption,
% 3.65/0.96                [status(thm)],
% 3.65/0.96                [c_1746,c_17]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1828,plain,
% 3.65/0.96      ( v1_tops_2(X0,sK3)
% 3.65/0.96      | ~ r2_hidden(sK2(sK3,X0),sK5)
% 3.65/0.96      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_1806,c_10]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_5132,plain,
% 3.65/0.96      ( v1_tops_2(k2_xboole_0(sK4,sK5),sK3)
% 3.65/0.96      | ~ r1_tarski(k2_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.96      inference(resolution,[status(thm)],[c_4815,c_1828]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_9,plain,
% 3.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.65/0.96      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.65/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_166,plain,
% 3.65/0.96      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.65/0.96      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_167,plain,
% 3.65/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.65/0.96      inference(renaming,[status(thm)],[c_166]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_210,plain,
% 3.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.96      | ~ r1_tarski(X2,X1)
% 3.65/0.96      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 3.65/0.96      inference(bin_hyper_res,[status(thm)],[c_9,c_167]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_578,plain,
% 3.65/0.96      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.65/0.96      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_579,plain,
% 3.65/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.65/0.96      inference(renaming,[status(thm)],[c_578]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_617,plain,
% 3.65/0.96      ( ~ r1_tarski(X0,X1)
% 3.65/0.96      | ~ r1_tarski(X2,X1)
% 3.65/0.96      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 3.65/0.96      inference(bin_hyper_res,[status(thm)],[c_210,c_579]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1647,plain,
% 3.65/0.96      ( ~ r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.96      | ~ r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.96      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) = k2_xboole_0(sK4,sK5) ),
% 3.65/0.96      inference(instantiation,[status(thm)],[c_617]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_697,plain,
% 3.65/0.96      ( ~ v1_tops_2(X0,X1) | v1_tops_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.65/0.96      theory(equality) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1630,plain,
% 3.65/0.96      ( ~ v1_tops_2(X0,X1)
% 3.65/0.96      | v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
% 3.65/0.96      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != X0
% 3.65/0.96      | sK3 != X1 ),
% 3.65/0.96      inference(instantiation,[status(thm)],[c_697]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1646,plain,
% 3.65/0.96      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
% 3.65/0.96      | ~ v1_tops_2(k2_xboole_0(sK4,sK5),X0)
% 3.65/0.96      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != k2_xboole_0(sK4,sK5)
% 3.65/0.96      | sK3 != X0 ),
% 3.65/0.96      inference(instantiation,[status(thm)],[c_1630]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_1649,plain,
% 3.65/0.96      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
% 3.65/0.96      | ~ v1_tops_2(k2_xboole_0(sK4,sK5),sK3)
% 3.65/0.96      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != k2_xboole_0(sK4,sK5)
% 3.65/0.96      | sK3 != sK3 ),
% 3.65/0.96      inference(instantiation,[status(thm)],[c_1646]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_691,plain,( X0 = X0 ),theory(equality) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_708,plain,
% 3.65/0.96      ( sK3 = sK3 ),
% 3.65/0.96      inference(instantiation,[status(thm)],[c_691]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(c_16,negated_conjecture,
% 3.65/0.96      ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
% 3.65/0.96      inference(cnf_transformation,[],[f54]) ).
% 3.65/0.96  
% 3.65/0.96  cnf(contradiction,plain,
% 3.65/0.96      ( $false ),
% 3.65/0.96      inference(minisat,
% 3.65/0.96                [status(thm)],
% 3.65/0.96                [c_8144,c_5132,c_1647,c_1649,c_1445,c_1443,c_708,c_16]) ).
% 3.65/0.96  
% 3.65/0.96  
% 3.65/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.96  
% 3.65/0.96  ------                               Statistics
% 3.65/0.96  
% 3.65/0.96  ------ Selected
% 3.65/0.96  
% 3.65/0.96  total_time:                             0.289
% 3.65/0.96  
%------------------------------------------------------------------------------

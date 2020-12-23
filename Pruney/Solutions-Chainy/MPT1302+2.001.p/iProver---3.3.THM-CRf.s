%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:22 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  161 (2508 expanded)
%              Number of clauses        :  103 ( 838 expanded)
%              Number of leaves         :   14 ( 562 expanded)
%              Depth                    :   34
%              Number of atoms          :  561 (13884 expanded)
%              Number of equality atoms :  182 (2259 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & v1_tops_2(X1,X0) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & v1_tops_2(X1,X0) )
                 => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X2,X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK4),X0)
        & v1_tops_2(sK4,X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK3,X2),X0)
            & v1_tops_2(X2,X0)
            & v1_tops_2(sK3,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X1,X2),sK2)
              & v1_tops_2(X2,sK2)
              & v1_tops_2(X1,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
    & v1_tops_2(sK4,sK2)
    & v1_tops_2(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f32,f31,f30])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    v1_tops_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f58,plain,(
    ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_607,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1515,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(k2_xboole_0(X2,X3),X4)
    | X1 != X4
    | X0 != k2_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_1878,plain,
    ( v1_tops_2(k4_subset_1(X0,X1,X2),X3)
    | ~ v1_tops_2(k2_xboole_0(X1,X2),X4)
    | X3 != X4
    | k4_subset_1(X0,X1,X2) != k2_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_3330,plain,
    ( v1_tops_2(k4_subset_1(X0,X1,sK4),X2)
    | ~ v1_tops_2(k2_xboole_0(X1,sK4),X3)
    | X2 != X3
    | k4_subset_1(X0,X1,sK4) != k2_xboole_0(X1,sK4) ),
    inference(instantiation,[status(thm)],[c_1878])).

cnf(c_17946,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),X0)
    | ~ v1_tops_2(k2_xboole_0(sK3,sK4),X1)
    | X0 != X1
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3330])).

cnf(c_17948,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
    | ~ v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_17946])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_182,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_183])).

cnf(c_480,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_481,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_522,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_229,c_481])).

cnf(c_5748,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK4,X1)
    | k4_subset_1(X1,X0,sK4) = k2_xboole_0(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_16354,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,sK4) = k2_xboole_0(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_5748])).

cnf(c_16720,plain,
    ( ~ r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_16354])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1119,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1106,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1535,plain,
    ( r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1106,c_1110])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1113,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1838,plain,
    ( k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1535,c_1113])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1117,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2256,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1117])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1118,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1121,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3053,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = X1
    | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),X1),X1) != iProver_top
    | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2256,c_1121])).

cnf(c_4389,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(X1,X2)
    | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X1,X2)),X2) != iProver_top
    | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X1,X2)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_3053])).

cnf(c_7246,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(X1,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2256,c_4389])).

cnf(c_7447,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_7246])).

cnf(c_7469,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7447,c_1838])).

cnf(c_7483,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7469,c_1118])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1116,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7498,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7483,c_1116])).

cnf(c_11115,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7498,c_1121])).

cnf(c_11184,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11115,c_1838])).

cnf(c_11217,plain,
    ( r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
    | k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11184,c_7483])).

cnf(c_11218,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11217])).

cnf(c_11231,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11218,c_1116])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1536,plain,
    ( r1_tarski(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1110])).

cnf(c_1839,plain,
    ( k2_xboole_0(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1536,c_1113])).

cnf(c_2257,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_1117])).

cnf(c_3052,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = X1
    | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),X1),X1) != iProver_top
    | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2257,c_1121])).

cnf(c_11488,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11231,c_3052])).

cnf(c_11518,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11488,c_1838])).

cnf(c_12305,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11518,c_7483])).

cnf(c_7499,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7483,c_3053])).

cnf(c_7503,plain,
    ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
    | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7499,c_1838])).

cnf(c_12333,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_12305,c_7503])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1112,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12951,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12333,c_1112])).

cnf(c_1111,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_381,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_382,plain,
    ( v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_1102,plain,
    ( v1_tops_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_2136,plain,
    ( v1_tops_2(X0,sK2) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_1102])).

cnf(c_15240,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12951,c_2136])).

cnf(c_16190,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_15240,c_1116])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(sK1(X0,X1),X0)
    | v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_315,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X4,X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | sK1(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_316,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_17,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_332,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_316,c_17])).

cnf(c_347,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(sK1(X1,X2),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_24])).

cnf(c_348,plain,
    ( ~ v1_tops_2(X0,sK2)
    | v1_tops_2(X1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK1(sK2,X1),X0) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_1104,plain,
    ( v1_tops_2(X0,sK2) != iProver_top
    | v1_tops_2(X1,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_2137,plain,
    ( v1_tops_2(X0,sK2) != iProver_top
    | v1_tops_2(X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_1104])).

cnf(c_2573,plain,
    ( v1_tops_2(X0,sK2) = iProver_top
    | v1_tops_2(sK4,sK2) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1106,c_2137])).

cnf(c_20,negated_conjecture,
    ( v1_tops_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,plain,
    ( v1_tops_2(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2609,plain,
    ( v1_tops_2(X0,sK2) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,X0),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2573,c_29])).

cnf(c_16413,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_16190,c_2609])).

cnf(c_16422,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16413,c_12951])).

cnf(c_2574,plain,
    ( v1_tops_2(X0,sK2) = iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_2137])).

cnf(c_21,negated_conjecture,
    ( v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,plain,
    ( v1_tops_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2704,plain,
    ( v1_tops_2(X0,sK2) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,X0),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_28])).

cnf(c_16429,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16422,c_2704])).

cnf(c_16434,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
    | ~ r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16429])).

cnf(c_13191,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12951])).

cnf(c_1549,plain,
    ( r1_tarski(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1536])).

cnf(c_1548,plain,
    ( r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1535])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_63,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_59,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_19,negated_conjecture,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17948,c_16720,c_16434,c_13191,c_1549,c_1548,c_63,c_59,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.08/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/0.98  
% 4.08/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.08/0.98  
% 4.08/0.98  ------  iProver source info
% 4.08/0.98  
% 4.08/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.08/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.08/0.98  git: non_committed_changes: false
% 4.08/0.98  git: last_make_outside_of_git: false
% 4.08/0.98  
% 4.08/0.98  ------ 
% 4.08/0.98  
% 4.08/0.98  ------ Input Options
% 4.08/0.98  
% 4.08/0.98  --out_options                           all
% 4.08/0.98  --tptp_safe_out                         true
% 4.08/0.98  --problem_path                          ""
% 4.08/0.98  --include_path                          ""
% 4.08/0.98  --clausifier                            res/vclausify_rel
% 4.08/0.98  --clausifier_options                    --mode clausify
% 4.08/0.98  --stdin                                 false
% 4.08/0.98  --stats_out                             all
% 4.08/0.98  
% 4.08/0.98  ------ General Options
% 4.08/0.98  
% 4.08/0.98  --fof                                   false
% 4.08/0.98  --time_out_real                         305.
% 4.08/0.98  --time_out_virtual                      -1.
% 4.08/0.98  --symbol_type_check                     false
% 4.08/0.98  --clausify_out                          false
% 4.08/0.98  --sig_cnt_out                           false
% 4.08/0.98  --trig_cnt_out                          false
% 4.08/0.98  --trig_cnt_out_tolerance                1.
% 4.08/0.98  --trig_cnt_out_sk_spl                   false
% 4.08/0.98  --abstr_cl_out                          false
% 4.08/0.98  
% 4.08/0.98  ------ Global Options
% 4.08/0.98  
% 4.08/0.98  --schedule                              default
% 4.08/0.98  --add_important_lit                     false
% 4.08/0.98  --prop_solver_per_cl                    1000
% 4.08/0.98  --min_unsat_core                        false
% 4.08/0.98  --soft_assumptions                      false
% 4.08/0.98  --soft_lemma_size                       3
% 4.08/0.98  --prop_impl_unit_size                   0
% 4.08/0.98  --prop_impl_unit                        []
% 4.08/0.98  --share_sel_clauses                     true
% 4.08/0.98  --reset_solvers                         false
% 4.08/0.98  --bc_imp_inh                            [conj_cone]
% 4.08/0.98  --conj_cone_tolerance                   3.
% 4.08/0.98  --extra_neg_conj                        none
% 4.08/0.98  --large_theory_mode                     true
% 4.08/0.98  --prolific_symb_bound                   200
% 4.08/0.98  --lt_threshold                          2000
% 4.08/0.98  --clause_weak_htbl                      true
% 4.08/0.98  --gc_record_bc_elim                     false
% 4.08/0.98  
% 4.08/0.98  ------ Preprocessing Options
% 4.08/0.98  
% 4.08/0.98  --preprocessing_flag                    true
% 4.08/0.98  --time_out_prep_mult                    0.1
% 4.08/0.98  --splitting_mode                        input
% 4.08/0.98  --splitting_grd                         true
% 4.08/0.98  --splitting_cvd                         false
% 4.08/0.98  --splitting_cvd_svl                     false
% 4.08/0.98  --splitting_nvd                         32
% 4.08/0.98  --sub_typing                            true
% 4.08/0.98  --prep_gs_sim                           true
% 4.08/0.98  --prep_unflatten                        true
% 4.08/0.98  --prep_res_sim                          true
% 4.08/0.98  --prep_upred                            true
% 4.08/0.98  --prep_sem_filter                       exhaustive
% 4.08/0.98  --prep_sem_filter_out                   false
% 4.08/0.98  --pred_elim                             true
% 4.08/0.98  --res_sim_input                         true
% 4.08/0.98  --eq_ax_congr_red                       true
% 4.08/0.98  --pure_diseq_elim                       true
% 4.08/0.98  --brand_transform                       false
% 4.08/0.98  --non_eq_to_eq                          false
% 4.08/0.98  --prep_def_merge                        true
% 4.08/0.98  --prep_def_merge_prop_impl              false
% 4.08/0.98  --prep_def_merge_mbd                    true
% 4.08/0.98  --prep_def_merge_tr_red                 false
% 4.08/0.98  --prep_def_merge_tr_cl                  false
% 4.08/0.98  --smt_preprocessing                     true
% 4.08/0.98  --smt_ac_axioms                         fast
% 4.08/0.98  --preprocessed_out                      false
% 4.08/0.98  --preprocessed_stats                    false
% 4.08/0.98  
% 4.08/0.98  ------ Abstraction refinement Options
% 4.08/0.98  
% 4.08/0.98  --abstr_ref                             []
% 4.08/0.98  --abstr_ref_prep                        false
% 4.08/0.98  --abstr_ref_until_sat                   false
% 4.08/0.98  --abstr_ref_sig_restrict                funpre
% 4.08/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.08/0.98  --abstr_ref_under                       []
% 4.08/0.98  
% 4.08/0.98  ------ SAT Options
% 4.08/0.98  
% 4.08/0.98  --sat_mode                              false
% 4.08/0.98  --sat_fm_restart_options                ""
% 4.08/0.98  --sat_gr_def                            false
% 4.08/0.98  --sat_epr_types                         true
% 4.08/0.98  --sat_non_cyclic_types                  false
% 4.08/0.98  --sat_finite_models                     false
% 4.08/0.98  --sat_fm_lemmas                         false
% 4.08/0.98  --sat_fm_prep                           false
% 4.08/0.98  --sat_fm_uc_incr                        true
% 4.08/0.98  --sat_out_model                         small
% 4.08/0.98  --sat_out_clauses                       false
% 4.08/0.98  
% 4.08/0.98  ------ QBF Options
% 4.08/0.98  
% 4.08/0.98  --qbf_mode                              false
% 4.08/0.98  --qbf_elim_univ                         false
% 4.08/0.98  --qbf_dom_inst                          none
% 4.08/0.98  --qbf_dom_pre_inst                      false
% 4.08/0.98  --qbf_sk_in                             false
% 4.08/0.98  --qbf_pred_elim                         true
% 4.08/0.98  --qbf_split                             512
% 4.08/0.98  
% 4.08/0.98  ------ BMC1 Options
% 4.08/0.98  
% 4.08/0.98  --bmc1_incremental                      false
% 4.08/0.98  --bmc1_axioms                           reachable_all
% 4.08/0.98  --bmc1_min_bound                        0
% 4.08/0.98  --bmc1_max_bound                        -1
% 4.08/0.98  --bmc1_max_bound_default                -1
% 4.08/0.98  --bmc1_symbol_reachability              true
% 4.08/0.98  --bmc1_property_lemmas                  false
% 4.08/0.98  --bmc1_k_induction                      false
% 4.08/0.98  --bmc1_non_equiv_states                 false
% 4.08/0.98  --bmc1_deadlock                         false
% 4.08/0.98  --bmc1_ucm                              false
% 4.08/0.98  --bmc1_add_unsat_core                   none
% 4.08/0.98  --bmc1_unsat_core_children              false
% 4.08/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.08/0.98  --bmc1_out_stat                         full
% 4.08/0.98  --bmc1_ground_init                      false
% 4.08/0.98  --bmc1_pre_inst_next_state              false
% 4.08/0.98  --bmc1_pre_inst_state                   false
% 4.08/0.98  --bmc1_pre_inst_reach_state             false
% 4.08/0.98  --bmc1_out_unsat_core                   false
% 4.08/0.98  --bmc1_aig_witness_out                  false
% 4.08/0.98  --bmc1_verbose                          false
% 4.08/0.98  --bmc1_dump_clauses_tptp                false
% 4.08/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.08/0.98  --bmc1_dump_file                        -
% 4.08/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.08/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.08/0.98  --bmc1_ucm_extend_mode                  1
% 4.08/0.98  --bmc1_ucm_init_mode                    2
% 4.08/0.98  --bmc1_ucm_cone_mode                    none
% 4.08/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.08/0.98  --bmc1_ucm_relax_model                  4
% 4.08/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.08/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.08/0.98  --bmc1_ucm_layered_model                none
% 4.08/0.98  --bmc1_ucm_max_lemma_size               10
% 4.08/0.98  
% 4.08/0.98  ------ AIG Options
% 4.08/0.98  
% 4.08/0.98  --aig_mode                              false
% 4.08/0.98  
% 4.08/0.98  ------ Instantiation Options
% 4.08/0.98  
% 4.08/0.98  --instantiation_flag                    true
% 4.08/0.98  --inst_sos_flag                         false
% 4.08/0.98  --inst_sos_phase                        true
% 4.08/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.08/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.08/0.98  --inst_lit_sel_side                     num_symb
% 4.08/0.98  --inst_solver_per_active                1400
% 4.08/0.98  --inst_solver_calls_frac                1.
% 4.08/0.98  --inst_passive_queue_type               priority_queues
% 4.08/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.08/0.98  --inst_passive_queues_freq              [25;2]
% 4.08/0.98  --inst_dismatching                      true
% 4.08/0.98  --inst_eager_unprocessed_to_passive     true
% 4.08/0.98  --inst_prop_sim_given                   true
% 4.08/0.98  --inst_prop_sim_new                     false
% 4.08/0.98  --inst_subs_new                         false
% 4.08/0.98  --inst_eq_res_simp                      false
% 4.08/0.98  --inst_subs_given                       false
% 4.08/0.98  --inst_orphan_elimination               true
% 4.08/0.98  --inst_learning_loop_flag               true
% 4.08/0.98  --inst_learning_start                   3000
% 4.08/0.98  --inst_learning_factor                  2
% 4.08/0.98  --inst_start_prop_sim_after_learn       3
% 4.08/0.98  --inst_sel_renew                        solver
% 4.08/0.98  --inst_lit_activity_flag                true
% 4.08/0.98  --inst_restr_to_given                   false
% 4.08/0.98  --inst_activity_threshold               500
% 4.08/0.98  --inst_out_proof                        true
% 4.08/0.98  
% 4.08/0.98  ------ Resolution Options
% 4.08/0.98  
% 4.08/0.98  --resolution_flag                       true
% 4.08/0.98  --res_lit_sel                           adaptive
% 4.08/0.98  --res_lit_sel_side                      none
% 4.08/0.98  --res_ordering                          kbo
% 4.08/0.98  --res_to_prop_solver                    active
% 4.08/0.98  --res_prop_simpl_new                    false
% 4.08/0.98  --res_prop_simpl_given                  true
% 4.08/0.98  --res_passive_queue_type                priority_queues
% 4.08/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.08/0.98  --res_passive_queues_freq               [15;5]
% 4.08/0.98  --res_forward_subs                      full
% 4.08/0.98  --res_backward_subs                     full
% 4.08/0.98  --res_forward_subs_resolution           true
% 4.08/0.98  --res_backward_subs_resolution          true
% 4.08/0.98  --res_orphan_elimination                true
% 4.08/0.98  --res_time_limit                        2.
% 4.08/0.98  --res_out_proof                         true
% 4.08/0.98  
% 4.08/0.98  ------ Superposition Options
% 4.08/0.98  
% 4.08/0.98  --superposition_flag                    true
% 4.08/0.98  --sup_passive_queue_type                priority_queues
% 4.08/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.08/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.08/0.98  --demod_completeness_check              fast
% 4.08/0.98  --demod_use_ground                      true
% 4.08/0.98  --sup_to_prop_solver                    passive
% 4.08/0.98  --sup_prop_simpl_new                    true
% 4.08/0.98  --sup_prop_simpl_given                  true
% 4.08/0.98  --sup_fun_splitting                     false
% 4.08/0.98  --sup_smt_interval                      50000
% 4.08/0.98  
% 4.08/0.98  ------ Superposition Simplification Setup
% 4.08/0.98  
% 4.08/0.98  --sup_indices_passive                   []
% 4.08/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.08/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.98  --sup_full_bw                           [BwDemod]
% 4.08/0.98  --sup_immed_triv                        [TrivRules]
% 4.08/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.98  --sup_immed_bw_main                     []
% 4.08/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.08/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/0.98  
% 4.08/0.98  ------ Combination Options
% 4.08/0.98  
% 4.08/0.98  --comb_res_mult                         3
% 4.08/0.98  --comb_sup_mult                         2
% 4.08/0.98  --comb_inst_mult                        10
% 4.08/0.98  
% 4.08/0.98  ------ Debug Options
% 4.08/0.98  
% 4.08/0.98  --dbg_backtrace                         false
% 4.08/0.98  --dbg_dump_prop_clauses                 false
% 4.08/0.98  --dbg_dump_prop_clauses_file            -
% 4.08/0.98  --dbg_out_stat                          false
% 4.08/0.98  ------ Parsing...
% 4.08/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.08/0.98  
% 4.08/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.08/0.98  
% 4.08/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.08/0.98  
% 4.08/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.08/0.98  ------ Proving...
% 4.08/0.98  ------ Problem Properties 
% 4.08/0.98  
% 4.08/0.98  
% 4.08/0.98  clauses                                 22
% 4.08/0.98  conjectures                             5
% 4.08/0.98  EPR                                     4
% 4.08/0.98  Horn                                    18
% 4.08/0.98  unary                                   8
% 4.08/0.98  binary                                  5
% 4.08/0.98  lits                                    48
% 4.08/0.98  lits eq                                 7
% 4.08/0.98  fd_pure                                 0
% 4.08/0.98  fd_pseudo                               0
% 4.08/0.98  fd_cond                                 0
% 4.08/0.98  fd_pseudo_cond                          4
% 4.08/0.98  AC symbols                              0
% 4.08/0.98  
% 4.08/0.98  ------ Schedule dynamic 5 is on 
% 4.08/0.98  
% 4.08/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.08/0.98  
% 4.08/0.98  
% 4.08/0.98  ------ 
% 4.08/0.98  Current options:
% 4.08/0.98  ------ 
% 4.08/0.98  
% 4.08/0.98  ------ Input Options
% 4.08/0.98  
% 4.08/0.98  --out_options                           all
% 4.08/0.98  --tptp_safe_out                         true
% 4.08/0.98  --problem_path                          ""
% 4.08/0.98  --include_path                          ""
% 4.08/0.98  --clausifier                            res/vclausify_rel
% 4.08/0.98  --clausifier_options                    --mode clausify
% 4.08/0.98  --stdin                                 false
% 4.08/0.98  --stats_out                             all
% 4.08/0.98  
% 4.08/0.98  ------ General Options
% 4.08/0.98  
% 4.08/0.98  --fof                                   false
% 4.08/0.98  --time_out_real                         305.
% 4.08/0.98  --time_out_virtual                      -1.
% 4.08/0.98  --symbol_type_check                     false
% 4.08/0.98  --clausify_out                          false
% 4.08/0.98  --sig_cnt_out                           false
% 4.08/0.98  --trig_cnt_out                          false
% 4.08/0.98  --trig_cnt_out_tolerance                1.
% 4.08/0.98  --trig_cnt_out_sk_spl                   false
% 4.08/0.98  --abstr_cl_out                          false
% 4.08/0.98  
% 4.08/0.98  ------ Global Options
% 4.08/0.98  
% 4.08/0.98  --schedule                              default
% 4.08/0.98  --add_important_lit                     false
% 4.08/0.98  --prop_solver_per_cl                    1000
% 4.08/0.98  --min_unsat_core                        false
% 4.08/0.98  --soft_assumptions                      false
% 4.08/0.98  --soft_lemma_size                       3
% 4.08/0.98  --prop_impl_unit_size                   0
% 4.08/0.98  --prop_impl_unit                        []
% 4.08/0.98  --share_sel_clauses                     true
% 4.08/0.98  --reset_solvers                         false
% 4.08/0.98  --bc_imp_inh                            [conj_cone]
% 4.08/0.98  --conj_cone_tolerance                   3.
% 4.08/0.98  --extra_neg_conj                        none
% 4.08/0.98  --large_theory_mode                     true
% 4.08/0.98  --prolific_symb_bound                   200
% 4.08/0.98  --lt_threshold                          2000
% 4.08/0.98  --clause_weak_htbl                      true
% 4.08/0.98  --gc_record_bc_elim                     false
% 4.08/0.98  
% 4.08/0.98  ------ Preprocessing Options
% 4.08/0.98  
% 4.08/0.98  --preprocessing_flag                    true
% 4.08/0.98  --time_out_prep_mult                    0.1
% 4.08/0.98  --splitting_mode                        input
% 4.08/0.98  --splitting_grd                         true
% 4.08/0.98  --splitting_cvd                         false
% 4.08/0.98  --splitting_cvd_svl                     false
% 4.08/0.98  --splitting_nvd                         32
% 4.08/0.98  --sub_typing                            true
% 4.08/0.98  --prep_gs_sim                           true
% 4.08/0.98  --prep_unflatten                        true
% 4.08/0.98  --prep_res_sim                          true
% 4.08/0.98  --prep_upred                            true
% 4.08/0.98  --prep_sem_filter                       exhaustive
% 4.08/0.98  --prep_sem_filter_out                   false
% 4.08/0.98  --pred_elim                             true
% 4.08/0.98  --res_sim_input                         true
% 4.08/0.98  --eq_ax_congr_red                       true
% 4.08/0.98  --pure_diseq_elim                       true
% 4.08/0.98  --brand_transform                       false
% 4.08/0.98  --non_eq_to_eq                          false
% 4.08/0.98  --prep_def_merge                        true
% 4.08/0.98  --prep_def_merge_prop_impl              false
% 4.08/0.98  --prep_def_merge_mbd                    true
% 4.08/0.98  --prep_def_merge_tr_red                 false
% 4.08/0.98  --prep_def_merge_tr_cl                  false
% 4.08/0.98  --smt_preprocessing                     true
% 4.08/0.98  --smt_ac_axioms                         fast
% 4.08/0.98  --preprocessed_out                      false
% 4.08/0.98  --preprocessed_stats                    false
% 4.08/0.98  
% 4.08/0.98  ------ Abstraction refinement Options
% 4.08/0.98  
% 4.08/0.98  --abstr_ref                             []
% 4.08/0.98  --abstr_ref_prep                        false
% 4.08/0.98  --abstr_ref_until_sat                   false
% 4.08/0.98  --abstr_ref_sig_restrict                funpre
% 4.08/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.08/0.98  --abstr_ref_under                       []
% 4.08/0.98  
% 4.08/0.98  ------ SAT Options
% 4.08/0.98  
% 4.08/0.98  --sat_mode                              false
% 4.08/0.98  --sat_fm_restart_options                ""
% 4.08/0.98  --sat_gr_def                            false
% 4.08/0.98  --sat_epr_types                         true
% 4.08/0.98  --sat_non_cyclic_types                  false
% 4.08/0.98  --sat_finite_models                     false
% 4.08/0.98  --sat_fm_lemmas                         false
% 4.08/0.98  --sat_fm_prep                           false
% 4.08/0.98  --sat_fm_uc_incr                        true
% 4.08/0.98  --sat_out_model                         small
% 4.08/0.98  --sat_out_clauses                       false
% 4.08/0.98  
% 4.08/0.98  ------ QBF Options
% 4.08/0.98  
% 4.08/0.98  --qbf_mode                              false
% 4.08/0.98  --qbf_elim_univ                         false
% 4.08/0.98  --qbf_dom_inst                          none
% 4.08/0.98  --qbf_dom_pre_inst                      false
% 4.08/0.98  --qbf_sk_in                             false
% 4.08/0.98  --qbf_pred_elim                         true
% 4.08/0.98  --qbf_split                             512
% 4.08/0.98  
% 4.08/0.98  ------ BMC1 Options
% 4.08/0.98  
% 4.08/0.98  --bmc1_incremental                      false
% 4.08/0.98  --bmc1_axioms                           reachable_all
% 4.08/0.98  --bmc1_min_bound                        0
% 4.08/0.98  --bmc1_max_bound                        -1
% 4.08/0.98  --bmc1_max_bound_default                -1
% 4.08/0.98  --bmc1_symbol_reachability              true
% 4.08/0.98  --bmc1_property_lemmas                  false
% 4.08/0.98  --bmc1_k_induction                      false
% 4.08/0.98  --bmc1_non_equiv_states                 false
% 4.08/0.98  --bmc1_deadlock                         false
% 4.08/0.98  --bmc1_ucm                              false
% 4.08/0.98  --bmc1_add_unsat_core                   none
% 4.08/0.98  --bmc1_unsat_core_children              false
% 4.08/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.08/0.98  --bmc1_out_stat                         full
% 4.08/0.98  --bmc1_ground_init                      false
% 4.08/0.98  --bmc1_pre_inst_next_state              false
% 4.08/0.98  --bmc1_pre_inst_state                   false
% 4.08/0.98  --bmc1_pre_inst_reach_state             false
% 4.08/0.98  --bmc1_out_unsat_core                   false
% 4.08/0.98  --bmc1_aig_witness_out                  false
% 4.08/0.98  --bmc1_verbose                          false
% 4.08/0.98  --bmc1_dump_clauses_tptp                false
% 4.08/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.08/0.98  --bmc1_dump_file                        -
% 4.08/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.08/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.08/0.98  --bmc1_ucm_extend_mode                  1
% 4.08/0.98  --bmc1_ucm_init_mode                    2
% 4.08/0.98  --bmc1_ucm_cone_mode                    none
% 4.08/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.08/0.98  --bmc1_ucm_relax_model                  4
% 4.08/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.08/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.08/0.98  --bmc1_ucm_layered_model                none
% 4.08/0.98  --bmc1_ucm_max_lemma_size               10
% 4.08/0.98  
% 4.08/0.98  ------ AIG Options
% 4.08/0.98  
% 4.08/0.98  --aig_mode                              false
% 4.08/0.98  
% 4.08/0.98  ------ Instantiation Options
% 4.08/0.98  
% 4.08/0.98  --instantiation_flag                    true
% 4.08/0.98  --inst_sos_flag                         false
% 4.08/0.98  --inst_sos_phase                        true
% 4.08/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.08/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.08/0.98  --inst_lit_sel_side                     none
% 4.08/0.98  --inst_solver_per_active                1400
% 4.08/0.98  --inst_solver_calls_frac                1.
% 4.08/0.98  --inst_passive_queue_type               priority_queues
% 4.08/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.08/0.98  --inst_passive_queues_freq              [25;2]
% 4.08/0.98  --inst_dismatching                      true
% 4.08/0.98  --inst_eager_unprocessed_to_passive     true
% 4.08/0.98  --inst_prop_sim_given                   true
% 4.08/0.98  --inst_prop_sim_new                     false
% 4.08/0.98  --inst_subs_new                         false
% 4.08/0.98  --inst_eq_res_simp                      false
% 4.08/0.98  --inst_subs_given                       false
% 4.08/0.98  --inst_orphan_elimination               true
% 4.08/0.98  --inst_learning_loop_flag               true
% 4.08/0.98  --inst_learning_start                   3000
% 4.08/0.98  --inst_learning_factor                  2
% 4.08/0.98  --inst_start_prop_sim_after_learn       3
% 4.08/0.98  --inst_sel_renew                        solver
% 4.08/0.98  --inst_lit_activity_flag                true
% 4.08/0.98  --inst_restr_to_given                   false
% 4.08/0.98  --inst_activity_threshold               500
% 4.08/0.98  --inst_out_proof                        true
% 4.08/0.98  
% 4.08/0.98  ------ Resolution Options
% 4.08/0.98  
% 4.08/0.98  --resolution_flag                       false
% 4.08/0.98  --res_lit_sel                           adaptive
% 4.08/0.98  --res_lit_sel_side                      none
% 4.08/0.98  --res_ordering                          kbo
% 4.08/0.98  --res_to_prop_solver                    active
% 4.08/0.98  --res_prop_simpl_new                    false
% 4.08/0.98  --res_prop_simpl_given                  true
% 4.08/0.98  --res_passive_queue_type                priority_queues
% 4.08/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.08/0.98  --res_passive_queues_freq               [15;5]
% 4.08/0.98  --res_forward_subs                      full
% 4.08/0.98  --res_backward_subs                     full
% 4.08/0.98  --res_forward_subs_resolution           true
% 4.08/0.98  --res_backward_subs_resolution          true
% 4.08/0.98  --res_orphan_elimination                true
% 4.08/0.98  --res_time_limit                        2.
% 4.08/0.98  --res_out_proof                         true
% 4.08/0.98  
% 4.08/0.98  ------ Superposition Options
% 4.08/0.98  
% 4.08/0.98  --superposition_flag                    true
% 4.08/0.98  --sup_passive_queue_type                priority_queues
% 4.08/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.08/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.08/0.98  --demod_completeness_check              fast
% 4.08/0.98  --demod_use_ground                      true
% 4.08/0.98  --sup_to_prop_solver                    passive
% 4.08/0.98  --sup_prop_simpl_new                    true
% 4.08/0.98  --sup_prop_simpl_given                  true
% 4.08/0.98  --sup_fun_splitting                     false
% 4.08/0.98  --sup_smt_interval                      50000
% 4.08/0.98  
% 4.08/0.98  ------ Superposition Simplification Setup
% 4.08/0.98  
% 4.08/0.98  --sup_indices_passive                   []
% 4.08/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.08/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.98  --sup_full_bw                           [BwDemod]
% 4.08/0.98  --sup_immed_triv                        [TrivRules]
% 4.08/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.98  --sup_immed_bw_main                     []
% 4.08/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.08/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/0.98  
% 4.08/0.98  ------ Combination Options
% 4.08/0.98  
% 4.08/0.98  --comb_res_mult                         3
% 4.08/0.98  --comb_sup_mult                         2
% 4.08/0.98  --comb_inst_mult                        10
% 4.08/0.98  
% 4.08/0.98  ------ Debug Options
% 4.08/0.98  
% 4.08/0.98  --dbg_backtrace                         false
% 4.08/0.98  --dbg_dump_prop_clauses                 false
% 4.08/0.98  --dbg_dump_prop_clauses_file            -
% 4.08/0.98  --dbg_out_stat                          false
% 4.08/0.98  
% 4.08/0.98  
% 4.08/0.98  
% 4.08/0.98  
% 4.08/0.98  ------ Proving...
% 4.08/0.98  
% 4.08/0.98  
% 4.08/0.98  % SZS status Theorem for theBenchmark.p
% 4.08/0.98  
% 4.08/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.08/0.98  
% 4.08/0.98  fof(f6,axiom,(
% 4.08/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.98  
% 4.08/0.98  fof(f12,plain,(
% 4.08/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.08/0.98    inference(ennf_transformation,[],[f6])).
% 4.08/0.98  
% 4.08/0.98  fof(f13,plain,(
% 4.08/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.08/0.98    inference(flattening,[],[f12])).
% 4.08/0.98  
% 4.08/0.98  fof(f46,plain,(
% 4.08/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/0.98    inference(cnf_transformation,[],[f13])).
% 4.08/0.98  
% 4.08/0.98  fof(f7,axiom,(
% 4.08/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.98  
% 4.08/0.98  fof(f25,plain,(
% 4.08/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.08/0.98    inference(nnf_transformation,[],[f7])).
% 4.08/0.98  
% 4.08/0.98  fof(f48,plain,(
% 4.08/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f25])).
% 4.08/0.98  
% 4.08/0.98  fof(f2,axiom,(
% 4.08/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.98  
% 4.08/0.98  fof(f18,plain,(
% 4.08/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.08/0.98    inference(nnf_transformation,[],[f2])).
% 4.08/0.98  
% 4.08/0.98  fof(f19,plain,(
% 4.08/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.08/0.98    inference(flattening,[],[f18])).
% 4.08/0.98  
% 4.08/0.98  fof(f20,plain,(
% 4.08/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.08/0.98    inference(rectify,[],[f19])).
% 4.08/0.98  
% 4.08/0.98  fof(f21,plain,(
% 4.08/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.08/0.98    introduced(choice_axiom,[])).
% 4.08/0.98  
% 4.08/0.98  fof(f22,plain,(
% 4.08/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.08/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 4.08/0.98  
% 4.08/0.98  fof(f38,plain,(
% 4.08/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f22])).
% 4.08/0.98  
% 4.08/0.98  fof(f9,conjecture,(
% 4.08/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 4.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.98  
% 4.08/0.98  fof(f10,negated_conjecture,(
% 4.08/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 4.08/0.98    inference(negated_conjecture,[],[f9])).
% 4.08/0.98  
% 4.08/0.98  fof(f16,plain,(
% 4.08/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v1_tops_2(X2,X0) & v1_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 4.08/0.98    inference(ennf_transformation,[],[f10])).
% 4.08/0.98  
% 4.08/0.98  fof(f17,plain,(
% 4.08/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 4.08/0.98    inference(flattening,[],[f16])).
% 4.08/0.98  
% 4.08/0.98  fof(f32,plain,(
% 4.08/0.98    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK4),X0) & v1_tops_2(sK4,X0) & v1_tops_2(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 4.08/0.98    introduced(choice_axiom,[])).
% 4.08/0.98  
% 4.08/0.98  fof(f31,plain,(
% 4.08/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK3,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(sK3,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 4.08/0.98    introduced(choice_axiom,[])).
% 4.08/0.98  
% 4.08/0.98  fof(f30,plain,(
% 4.08/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X1,X2),sK2) & v1_tops_2(X2,sK2) & v1_tops_2(X1,sK2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 4.08/0.98    introduced(choice_axiom,[])).
% 4.08/0.98  
% 4.08/0.98  fof(f33,plain,(
% 4.08/0.98    ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) & v1_tops_2(sK4,sK2) & v1_tops_2(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 4.08/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f32,f31,f30])).
% 4.08/0.98  
% 4.08/0.98  fof(f55,plain,(
% 4.08/0.98    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 4.08/0.98    inference(cnf_transformation,[],[f33])).
% 4.08/0.98  
% 4.08/0.98  fof(f47,plain,(
% 4.08/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.08/0.98    inference(cnf_transformation,[],[f25])).
% 4.08/0.98  
% 4.08/0.98  fof(f4,axiom,(
% 4.08/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.98  
% 4.08/0.98  fof(f11,plain,(
% 4.08/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.08/0.98    inference(ennf_transformation,[],[f4])).
% 4.08/0.98  
% 4.08/0.98  fof(f44,plain,(
% 4.08/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f11])).
% 4.08/0.98  
% 4.08/0.98  fof(f36,plain,(
% 4.08/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 4.08/0.98    inference(cnf_transformation,[],[f22])).
% 4.08/0.98  
% 4.08/0.98  fof(f60,plain,(
% 4.08/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 4.08/0.98    inference(equality_resolution,[],[f36])).
% 4.08/0.98  
% 4.08/0.98  fof(f37,plain,(
% 4.08/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 4.08/0.98    inference(cnf_transformation,[],[f22])).
% 4.08/0.98  
% 4.08/0.98  fof(f59,plain,(
% 4.08/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 4.08/0.98    inference(equality_resolution,[],[f37])).
% 4.08/0.98  
% 4.08/0.98  fof(f40,plain,(
% 4.08/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f22])).
% 4.08/0.98  
% 4.08/0.98  fof(f35,plain,(
% 4.08/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 4.08/0.98    inference(cnf_transformation,[],[f22])).
% 4.08/0.98  
% 4.08/0.98  fof(f61,plain,(
% 4.08/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 4.08/0.98    inference(equality_resolution,[],[f35])).
% 4.08/0.98  
% 4.08/0.98  fof(f54,plain,(
% 4.08/0.98    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 4.08/0.98    inference(cnf_transformation,[],[f33])).
% 4.08/0.98  
% 4.08/0.98  fof(f5,axiom,(
% 4.08/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.98  
% 4.08/0.98  fof(f45,plain,(
% 4.08/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.08/0.98    inference(cnf_transformation,[],[f5])).
% 4.08/0.98  
% 4.08/0.98  fof(f8,axiom,(
% 4.08/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 4.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.98  
% 4.08/0.98  fof(f14,plain,(
% 4.08/0.98    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 4.08/0.98    inference(ennf_transformation,[],[f8])).
% 4.08/0.98  
% 4.08/0.98  fof(f15,plain,(
% 4.08/0.98    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 4.08/0.98    inference(flattening,[],[f14])).
% 4.08/0.98  
% 4.08/0.98  fof(f26,plain,(
% 4.08/0.98    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 4.08/0.98    inference(nnf_transformation,[],[f15])).
% 4.08/0.98  
% 4.08/0.98  fof(f27,plain,(
% 4.08/0.98    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 4.08/0.98    inference(rectify,[],[f26])).
% 4.08/0.98  
% 4.08/0.98  fof(f28,plain,(
% 4.08/0.98    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.08/0.98    introduced(choice_axiom,[])).
% 4.08/0.98  
% 4.08/0.98  fof(f29,plain,(
% 4.08/0.98    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 4.08/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 4.08/0.98  
% 4.08/0.98  fof(f51,plain,(
% 4.08/0.98    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f29])).
% 4.08/0.98  
% 4.08/0.98  fof(f53,plain,(
% 4.08/0.98    l1_pre_topc(sK2)),
% 4.08/0.98    inference(cnf_transformation,[],[f33])).
% 4.08/0.98  
% 4.08/0.98  fof(f52,plain,(
% 4.08/0.98    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f29])).
% 4.08/0.98  
% 4.08/0.98  fof(f49,plain,(
% 4.08/0.98    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f29])).
% 4.08/0.98  
% 4.08/0.98  fof(f50,plain,(
% 4.08/0.98    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f29])).
% 4.08/0.98  
% 4.08/0.98  fof(f57,plain,(
% 4.08/0.98    v1_tops_2(sK4,sK2)),
% 4.08/0.98    inference(cnf_transformation,[],[f33])).
% 4.08/0.98  
% 4.08/0.98  fof(f56,plain,(
% 4.08/0.98    v1_tops_2(sK3,sK2)),
% 4.08/0.98    inference(cnf_transformation,[],[f33])).
% 4.08/0.98  
% 4.08/0.98  fof(f3,axiom,(
% 4.08/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.98  
% 4.08/0.98  fof(f23,plain,(
% 4.08/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.08/0.98    inference(nnf_transformation,[],[f3])).
% 4.08/0.98  
% 4.08/0.98  fof(f24,plain,(
% 4.08/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.08/0.98    inference(flattening,[],[f23])).
% 4.08/0.98  
% 4.08/0.98  fof(f43,plain,(
% 4.08/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.08/0.98    inference(cnf_transformation,[],[f24])).
% 4.08/0.98  
% 4.08/0.98  fof(f41,plain,(
% 4.08/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.08/0.98    inference(cnf_transformation,[],[f24])).
% 4.08/0.98  
% 4.08/0.98  fof(f63,plain,(
% 4.08/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.08/0.98    inference(equality_resolution,[],[f41])).
% 4.08/0.98  
% 4.08/0.98  fof(f58,plain,(
% 4.08/0.98    ~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)),
% 4.08/0.98    inference(cnf_transformation,[],[f33])).
% 4.08/0.98  
% 4.08/0.98  cnf(c_607,plain,
% 4.08/0.98      ( ~ v1_tops_2(X0,X1) | v1_tops_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.08/0.98      theory(equality) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1515,plain,
% 4.08/0.98      ( v1_tops_2(X0,X1)
% 4.08/0.98      | ~ v1_tops_2(k2_xboole_0(X2,X3),X4)
% 4.08/0.98      | X1 != X4
% 4.08/0.98      | X0 != k2_xboole_0(X2,X3) ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_607]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1878,plain,
% 4.08/0.98      ( v1_tops_2(k4_subset_1(X0,X1,X2),X3)
% 4.08/0.98      | ~ v1_tops_2(k2_xboole_0(X1,X2),X4)
% 4.08/0.98      | X3 != X4
% 4.08/0.98      | k4_subset_1(X0,X1,X2) != k2_xboole_0(X1,X2) ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_1515]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_3330,plain,
% 4.08/0.98      ( v1_tops_2(k4_subset_1(X0,X1,sK4),X2)
% 4.08/0.98      | ~ v1_tops_2(k2_xboole_0(X1,sK4),X3)
% 4.08/0.98      | X2 != X3
% 4.08/0.98      | k4_subset_1(X0,X1,sK4) != k2_xboole_0(X1,sK4) ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_1878]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_17946,plain,
% 4.08/0.98      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),X0)
% 4.08/0.98      | ~ v1_tops_2(k2_xboole_0(sK3,sK4),X1)
% 4.08/0.98      | X0 != X1
% 4.08/0.98      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(sK3,sK4) ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_3330]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_17948,plain,
% 4.08/0.98      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
% 4.08/0.98      | ~ v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
% 4.08/0.98      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 4.08/0.98      | sK2 != sK2 ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_17946]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_12,plain,
% 4.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.08/0.98      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 4.08/0.98      inference(cnf_transformation,[],[f46]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_13,plain,
% 4.08/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.08/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_182,plain,
% 4.08/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.08/0.98      inference(prop_impl,[status(thm)],[c_13]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_183,plain,
% 4.08/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.08/0.98      inference(renaming,[status(thm)],[c_182]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_229,plain,
% 4.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.08/0.98      | ~ r1_tarski(X2,X1)
% 4.08/0.98      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 4.08/0.98      inference(bin_hyper_res,[status(thm)],[c_12,c_183]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_480,plain,
% 4.08/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.08/0.98      inference(prop_impl,[status(thm)],[c_13]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_481,plain,
% 4.08/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.08/0.98      inference(renaming,[status(thm)],[c_480]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_522,plain,
% 4.08/0.98      ( ~ r1_tarski(X0,X1)
% 4.08/0.98      | ~ r1_tarski(X2,X1)
% 4.08/0.98      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 4.08/0.98      inference(bin_hyper_res,[status(thm)],[c_229,c_481]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_5748,plain,
% 4.08/0.98      ( ~ r1_tarski(X0,X1)
% 4.08/0.98      | ~ r1_tarski(sK4,X1)
% 4.08/0.98      | k4_subset_1(X1,X0,sK4) = k2_xboole_0(X0,sK4) ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_522]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_16354,plain,
% 4.08/0.98      ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | ~ r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,sK4) = k2_xboole_0(X0,sK4) ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_5748]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_16720,plain,
% 4.08/0.98      ( ~ r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | ~ r1_tarski(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_16354]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_3,plain,
% 4.08/0.98      ( r2_hidden(sK0(X0,X1,X2),X1)
% 4.08/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 4.08/0.98      | r2_hidden(sK0(X0,X1,X2),X0)
% 4.08/0.98      | k2_xboole_0(X0,X1) = X2 ),
% 4.08/0.98      inference(cnf_transformation,[],[f38]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1119,plain,
% 4.08/0.98      ( k2_xboole_0(X0,X1) = X2
% 4.08/0.98      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_22,negated_conjecture,
% 4.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 4.08/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1106,plain,
% 4.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_14,plain,
% 4.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.08/0.98      inference(cnf_transformation,[],[f47]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1110,plain,
% 4.08/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.08/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1535,plain,
% 4.08/0.98      ( r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1106,c_1110]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_10,plain,
% 4.08/0.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 4.08/0.98      inference(cnf_transformation,[],[f44]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1113,plain,
% 4.08/0.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1838,plain,
% 4.08/0.98      ( k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1535,c_1113]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_5,plain,
% 4.08/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 4.08/0.98      inference(cnf_transformation,[],[f60]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1117,plain,
% 4.08/0.98      ( r2_hidden(X0,X1) != iProver_top
% 4.08/0.98      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_2256,plain,
% 4.08/0.98      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 4.08/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1838,c_1117]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_4,plain,
% 4.08/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 4.08/0.98      inference(cnf_transformation,[],[f59]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1118,plain,
% 4.08/0.98      ( r2_hidden(X0,X1) != iProver_top
% 4.08/0.98      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1,plain,
% 4.08/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 4.08/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 4.08/0.98      | k2_xboole_0(X0,X1) = X2 ),
% 4.08/0.98      inference(cnf_transformation,[],[f40]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1121,plain,
% 4.08/0.98      ( k2_xboole_0(X0,X1) = X2
% 4.08/0.98      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 4.08/0.98      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_3053,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = X1
% 4.08/0.98      | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),X1),X1) != iProver_top
% 4.08/0.98      | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),X1),sK4) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_2256,c_1121]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_4389,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(X1,X2)
% 4.08/0.98      | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X1,X2)),X2) != iProver_top
% 4.08/0.98      | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X1,X2)),sK4) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1118,c_3053]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_7246,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | r2_hidden(sK0(X1,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),sK4) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_2256,c_4389]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_7447,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1119,c_7246]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_7469,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 4.08/0.98      inference(light_normalisation,[status(thm)],[c_7447,c_1838]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_7483,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 4.08/0.98      inference(forward_subsumption_resolution,
% 4.08/0.98                [status(thm)],
% 4.08/0.98                [c_7469,c_1118]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_6,plain,
% 4.08/0.98      ( r2_hidden(X0,X1)
% 4.08/0.98      | r2_hidden(X0,X2)
% 4.08/0.98      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 4.08/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1116,plain,
% 4.08/0.98      ( r2_hidden(X0,X1) = iProver_top
% 4.08/0.98      | r2_hidden(X0,X2) = iProver_top
% 4.08/0.98      | r2_hidden(X0,k2_xboole_0(X1,X2)) != iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_7498,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_7483,c_1116]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_11115,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_7498,c_1121]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_11184,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 4.08/0.98      inference(light_normalisation,[status(thm)],[c_11115,c_1838]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_11217,plain,
% 4.08/0.98      ( r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
% 4.08/0.98      | k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 4.08/0.98      inference(global_propositional_subsumption,
% 4.08/0.98                [status(thm)],
% 4.08/0.98                [c_11184,c_7483]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_11218,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top ),
% 4.08/0.98      inference(renaming,[status(thm)],[c_11217]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_11231,plain,
% 4.08/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))),X1) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_11218,c_1116]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_23,negated_conjecture,
% 4.08/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 4.08/0.98      inference(cnf_transformation,[],[f54]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1105,plain,
% 4.08/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1536,plain,
% 4.08/0.98      ( r1_tarski(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1105,c_1110]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1839,plain,
% 4.08/0.98      ( k2_xboole_0(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1536,c_1113]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_2257,plain,
% 4.08/0.98      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 4.08/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1839,c_1117]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_3052,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = X1
% 4.08/0.98      | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),X1),X1) != iProver_top
% 4.08/0.98      | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK2)),X1),sK3) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_2257,c_1121]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_11488,plain,
% 4.08/0.98      ( k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_11231,c_3052]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_11518,plain,
% 4.08/0.98      ( k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 4.08/0.98      inference(light_normalisation,[status(thm)],[c_11488,c_1838]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_12305,plain,
% 4.08/0.98      ( k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(k2_xboole_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))),X0) = iProver_top ),
% 4.08/0.98      inference(forward_subsumption_resolution,
% 4.08/0.98                [status(thm)],
% 4.08/0.98                [c_11518,c_7483]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_7499,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k2_xboole_0(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 4.08/0.98      | k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),sK4) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_7483,c_3053]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_7503,plain,
% 4.08/0.98      ( k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2))
% 4.08/0.98      | r2_hidden(sK0(sK4,k1_zfmisc_1(u1_struct_0(sK2)),k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2)))),sK4) != iProver_top ),
% 4.08/0.98      inference(light_normalisation,[status(thm)],[c_7499,c_1838]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_12333,plain,
% 4.08/0.98      ( k2_xboole_0(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_12305,c_7503]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_11,plain,
% 4.08/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 4.08/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1112,plain,
% 4.08/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_12951,plain,
% 4.08/0.98      ( r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_12333,c_1112]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1111,plain,
% 4.08/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.08/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_16,plain,
% 4.08/0.98      ( v1_tops_2(X0,X1)
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | r2_hidden(sK1(X1,X0),X0)
% 4.08/0.98      | ~ l1_pre_topc(X1) ),
% 4.08/0.98      inference(cnf_transformation,[],[f51]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_24,negated_conjecture,
% 4.08/0.98      ( l1_pre_topc(sK2) ),
% 4.08/0.98      inference(cnf_transformation,[],[f53]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_381,plain,
% 4.08/0.98      ( v1_tops_2(X0,X1)
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | r2_hidden(sK1(X1,X0),X0)
% 4.08/0.98      | sK2 != X1 ),
% 4.08/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_382,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2)
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 4.08/0.98      | r2_hidden(sK1(sK2,X0),X0) ),
% 4.08/0.98      inference(unflattening,[status(thm)],[c_381]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1102,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2) = iProver_top
% 4.08/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,X0),X0) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_2136,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2) = iProver_top
% 4.08/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,X0),X0) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1111,c_1102]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_15240,plain,
% 4.08/0.98      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_12951,c_2136]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_16190,plain,
% 4.08/0.98      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4) = iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_15240,c_1116]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_15,plain,
% 4.08/0.98      ( ~ v3_pre_topc(sK1(X0,X1),X0)
% 4.08/0.98      | v1_tops_2(X1,X0)
% 4.08/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 4.08/0.98      | ~ l1_pre_topc(X0) ),
% 4.08/0.98      inference(cnf_transformation,[],[f52]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_18,plain,
% 4.08/0.98      ( v3_pre_topc(X0,X1)
% 4.08/0.98      | ~ v1_tops_2(X2,X1)
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | ~ r2_hidden(X0,X2)
% 4.08/0.98      | ~ l1_pre_topc(X1) ),
% 4.08/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_315,plain,
% 4.08/0.98      ( ~ v1_tops_2(X0,X1)
% 4.08/0.98      | v1_tops_2(X2,X3)
% 4.08/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | ~ r2_hidden(X4,X0)
% 4.08/0.98      | ~ l1_pre_topc(X3)
% 4.08/0.98      | ~ l1_pre_topc(X1)
% 4.08/0.98      | X1 != X3
% 4.08/0.98      | sK1(X3,X2) != X4 ),
% 4.08/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_316,plain,
% 4.08/0.98      ( ~ v1_tops_2(X0,X1)
% 4.08/0.98      | v1_tops_2(X2,X1)
% 4.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | ~ m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.98      | ~ r2_hidden(sK1(X1,X2),X0)
% 4.08/0.98      | ~ l1_pre_topc(X1) ),
% 4.08/0.98      inference(unflattening,[status(thm)],[c_315]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_17,plain,
% 4.08/0.98      ( v1_tops_2(X0,X1)
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.98      | ~ l1_pre_topc(X1) ),
% 4.08/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_332,plain,
% 4.08/0.98      ( ~ v1_tops_2(X0,X1)
% 4.08/0.98      | v1_tops_2(X2,X1)
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | ~ r2_hidden(sK1(X1,X2),X0)
% 4.08/0.98      | ~ l1_pre_topc(X1) ),
% 4.08/0.98      inference(forward_subsumption_resolution,
% 4.08/0.98                [status(thm)],
% 4.08/0.98                [c_316,c_17]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_347,plain,
% 4.08/0.98      ( ~ v1_tops_2(X0,X1)
% 4.08/0.98      | v1_tops_2(X2,X1)
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 4.08/0.98      | ~ r2_hidden(sK1(X1,X2),X0)
% 4.08/0.98      | sK2 != X1 ),
% 4.08/0.98      inference(resolution_lifted,[status(thm)],[c_332,c_24]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_348,plain,
% 4.08/0.98      ( ~ v1_tops_2(X0,sK2)
% 4.08/0.98      | v1_tops_2(X1,sK2)
% 4.08/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 4.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 4.08/0.98      | ~ r2_hidden(sK1(sK2,X1),X0) ),
% 4.08/0.98      inference(unflattening,[status(thm)],[c_347]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1104,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2) != iProver_top
% 4.08/0.98      | v1_tops_2(X1,sK2) = iProver_top
% 4.08/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 4.08/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,X1),X0) != iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_2137,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2) != iProver_top
% 4.08/0.98      | v1_tops_2(X1,sK2) = iProver_top
% 4.08/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 4.08/0.98      | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,X1),X0) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1111,c_1104]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_2573,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2) = iProver_top
% 4.08/0.98      | v1_tops_2(sK4,sK2) != iProver_top
% 4.08/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,X0),sK4) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1106,c_2137]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_20,negated_conjecture,
% 4.08/0.98      ( v1_tops_2(sK4,sK2) ),
% 4.08/0.98      inference(cnf_transformation,[],[f57]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_29,plain,
% 4.08/0.98      ( v1_tops_2(sK4,sK2) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_2609,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2) = iProver_top
% 4.08/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,X0),sK4) != iProver_top ),
% 4.08/0.98      inference(global_propositional_subsumption,
% 4.08/0.98                [status(thm)],
% 4.08/0.98                [c_2573,c_29]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_16413,plain,
% 4.08/0.98      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
% 4.08/0.98      | r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) = iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_16190,c_2609]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_16422,plain,
% 4.08/0.98      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) = iProver_top ),
% 4.08/0.98      inference(global_propositional_subsumption,
% 4.08/0.98                [status(thm)],
% 4.08/0.98                [c_16413,c_12951]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_2574,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2) = iProver_top
% 4.08/0.98      | v1_tops_2(sK3,sK2) != iProver_top
% 4.08/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,X0),sK3) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_1105,c_2137]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_21,negated_conjecture,
% 4.08/0.98      ( v1_tops_2(sK3,sK2) ),
% 4.08/0.98      inference(cnf_transformation,[],[f56]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_28,plain,
% 4.08/0.98      ( v1_tops_2(sK3,sK2) = iProver_top ),
% 4.08/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_2704,plain,
% 4.08/0.98      ( v1_tops_2(X0,sK2) = iProver_top
% 4.08/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 4.08/0.98      | r2_hidden(sK1(sK2,X0),sK3) != iProver_top ),
% 4.08/0.98      inference(global_propositional_subsumption,
% 4.08/0.98                [status(thm)],
% 4.08/0.98                [c_2574,c_28]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_16429,plain,
% 4.08/0.98      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
% 4.08/0.98      | r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 4.08/0.98      inference(superposition,[status(thm)],[c_16422,c_2704]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_16434,plain,
% 4.08/0.98      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
% 4.08/0.98      | ~ r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 4.08/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_16429]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_13191,plain,
% 4.08/0.98      ( r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 4.08/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_12951]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1549,plain,
% 4.08/0.98      ( r1_tarski(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 4.08/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1536]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_1548,plain,
% 4.08/0.98      ( r1_tarski(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 4.08/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1535]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_7,plain,
% 4.08/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.08/0.98      inference(cnf_transformation,[],[f43]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_63,plain,
% 4.08/0.98      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_9,plain,
% 4.08/0.98      ( r1_tarski(X0,X0) ),
% 4.08/0.98      inference(cnf_transformation,[],[f63]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_59,plain,
% 4.08/0.98      ( r1_tarski(sK2,sK2) ),
% 4.08/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(c_19,negated_conjecture,
% 4.08/0.98      ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) ),
% 4.08/0.98      inference(cnf_transformation,[],[f58]) ).
% 4.08/0.98  
% 4.08/0.98  cnf(contradiction,plain,
% 4.08/0.98      ( $false ),
% 4.08/0.98      inference(minisat,
% 4.08/0.98                [status(thm)],
% 4.08/0.98                [c_17948,c_16720,c_16434,c_13191,c_1549,c_1548,c_63,c_59,
% 4.08/0.98                 c_19]) ).
% 4.08/0.98  
% 4.08/0.98  
% 4.08/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.08/0.98  
% 4.08/0.98  ------                               Statistics
% 4.08/0.98  
% 4.08/0.98  ------ General
% 4.08/0.98  
% 4.08/0.98  abstr_ref_over_cycles:                  0
% 4.08/0.98  abstr_ref_under_cycles:                 0
% 4.08/0.98  gc_basic_clause_elim:                   0
% 4.08/0.98  forced_gc_time:                         0
% 4.08/0.98  parsing_time:                           0.009
% 4.08/0.98  unif_index_cands_time:                  0.
% 4.08/0.98  unif_index_add_time:                    0.
% 4.08/0.98  orderings_time:                         0.
% 4.08/0.98  out_proof_time:                         0.011
% 4.08/0.98  total_time:                             0.463
% 4.08/0.98  num_of_symbols:                         46
% 4.08/0.98  num_of_terms:                           12879
% 4.08/0.98  
% 4.08/0.98  ------ Preprocessing
% 4.08/0.98  
% 4.08/0.98  num_of_splits:                          0
% 4.08/0.98  num_of_split_atoms:                     0
% 4.08/0.98  num_of_reused_defs:                     0
% 4.08/0.98  num_eq_ax_congr_red:                    23
% 4.08/0.98  num_of_sem_filtered_clauses:            1
% 4.08/0.98  num_of_subtypes:                        0
% 4.08/0.98  monotx_restored_types:                  0
% 4.08/0.98  sat_num_of_epr_types:                   0
% 4.08/0.98  sat_num_of_non_cyclic_types:            0
% 4.08/0.98  sat_guarded_non_collapsed_types:        0
% 4.08/0.98  num_pure_diseq_elim:                    0
% 4.08/0.98  simp_replaced_by:                       0
% 4.08/0.98  res_preprocessed:                       111
% 4.08/0.98  prep_upred:                             0
% 4.08/0.98  prep_unflattend:                        5
% 4.08/0.98  smt_new_axioms:                         0
% 4.08/0.98  pred_elim_cands:                        4
% 4.08/0.98  pred_elim:                              2
% 4.08/0.98  pred_elim_cl:                           2
% 4.08/0.98  pred_elim_cycles:                       4
% 4.08/0.98  merged_defs:                            8
% 4.08/0.98  merged_defs_ncl:                        0
% 4.08/0.98  bin_hyper_res:                          10
% 4.08/0.98  prep_cycles:                            4
% 4.08/0.98  pred_elim_time:                         0.003
% 4.08/0.98  splitting_time:                         0.
% 4.08/0.98  sem_filter_time:                        0.
% 4.08/0.98  monotx_time:                            0.
% 4.08/0.98  subtype_inf_time:                       0.
% 4.08/0.98  
% 4.08/0.98  ------ Problem properties
% 4.08/0.98  
% 4.08/0.98  clauses:                                22
% 4.08/0.98  conjectures:                            5
% 4.08/0.98  epr:                                    4
% 4.08/0.98  horn:                                   18
% 4.08/0.98  ground:                                 5
% 4.08/0.98  unary:                                  8
% 4.08/0.98  binary:                                 5
% 4.08/0.98  lits:                                   48
% 4.08/0.98  lits_eq:                                7
% 4.08/0.98  fd_pure:                                0
% 4.08/0.98  fd_pseudo:                              0
% 4.08/0.98  fd_cond:                                0
% 4.08/0.98  fd_pseudo_cond:                         4
% 4.08/0.98  ac_symbols:                             0
% 4.08/0.98  
% 4.08/0.98  ------ Propositional Solver
% 4.08/0.98  
% 4.08/0.98  prop_solver_calls:                      32
% 4.08/0.98  prop_fast_solver_calls:                 1036
% 4.08/0.98  smt_solver_calls:                       0
% 4.08/0.98  smt_fast_solver_calls:                  0
% 4.08/0.98  prop_num_of_clauses:                    4619
% 4.08/0.98  prop_preprocess_simplified:             9063
% 4.08/0.98  prop_fo_subsumed:                       21
% 4.08/0.98  prop_solver_time:                       0.
% 4.08/0.98  smt_solver_time:                        0.
% 4.08/0.98  smt_fast_solver_time:                   0.
% 4.08/0.98  prop_fast_solver_time:                  0.
% 4.08/0.98  prop_unsat_core_time:                   0.
% 4.08/0.98  
% 4.08/0.98  ------ QBF
% 4.08/0.98  
% 4.08/0.98  qbf_q_res:                              0
% 4.08/0.98  qbf_num_tautologies:                    0
% 4.08/0.98  qbf_prep_cycles:                        0
% 4.08/0.98  
% 4.08/0.98  ------ BMC1
% 4.08/0.98  
% 4.08/0.98  bmc1_current_bound:                     -1
% 4.08/0.98  bmc1_last_solved_bound:                 -1
% 4.08/0.98  bmc1_unsat_core_size:                   -1
% 4.08/0.98  bmc1_unsat_core_parents_size:           -1
% 4.08/0.98  bmc1_merge_next_fun:                    0
% 4.08/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.08/0.98  
% 4.08/0.98  ------ Instantiation
% 4.08/0.98  
% 4.08/0.98  inst_num_of_clauses:                    1135
% 4.08/0.98  inst_num_in_passive:                    551
% 4.08/0.98  inst_num_in_active:                     582
% 4.08/0.98  inst_num_in_unprocessed:                1
% 4.08/0.98  inst_num_of_loops:                      802
% 4.08/0.98  inst_num_of_learning_restarts:          0
% 4.08/0.98  inst_num_moves_active_passive:          214
% 4.08/0.98  inst_lit_activity:                      0
% 4.08/0.98  inst_lit_activity_moves:                0
% 4.08/0.98  inst_num_tautologies:                   0
% 4.08/0.98  inst_num_prop_implied:                  0
% 4.08/0.98  inst_num_existing_simplified:           0
% 4.08/0.98  inst_num_eq_res_simplified:             0
% 4.08/0.98  inst_num_child_elim:                    0
% 4.08/0.98  inst_num_of_dismatching_blockings:      886
% 4.08/0.98  inst_num_of_non_proper_insts:           1858
% 4.08/0.98  inst_num_of_duplicates:                 0
% 4.08/0.98  inst_inst_num_from_inst_to_res:         0
% 4.08/0.98  inst_dismatching_checking_time:         0.
% 4.08/0.98  
% 4.08/0.98  ------ Resolution
% 4.08/0.98  
% 4.08/0.98  res_num_of_clauses:                     0
% 4.08/0.98  res_num_in_passive:                     0
% 4.08/0.98  res_num_in_active:                      0
% 4.08/0.98  res_num_of_loops:                       115
% 4.08/0.98  res_forward_subset_subsumed:            174
% 4.08/0.98  res_backward_subset_subsumed:           4
% 4.08/0.98  res_forward_subsumed:                   0
% 4.08/0.98  res_backward_subsumed:                  0
% 4.08/0.98  res_forward_subsumption_resolution:     1
% 4.08/0.98  res_backward_subsumption_resolution:    0
% 4.08/0.98  res_clause_to_clause_subsumption:       7818
% 4.08/0.98  res_orphan_elimination:                 0
% 4.08/0.98  res_tautology_del:                      183
% 4.08/0.98  res_num_eq_res_simplified:              0
% 4.08/0.98  res_num_sel_changes:                    0
% 4.08/0.98  res_moves_from_active_to_pass:          0
% 4.08/0.98  
% 4.08/0.98  ------ Superposition
% 4.08/0.98  
% 4.08/0.98  sup_time_total:                         0.
% 4.08/0.98  sup_time_generating:                    0.
% 4.08/0.98  sup_time_sim_full:                      0.
% 4.08/0.98  sup_time_sim_immed:                     0.
% 4.08/0.98  
% 4.08/0.98  sup_num_of_clauses:                     475
% 4.08/0.98  sup_num_in_active:                      147
% 4.08/0.98  sup_num_in_passive:                     328
% 4.08/0.98  sup_num_of_loops:                       160
% 4.08/0.98  sup_fw_superposition:                   1292
% 4.08/0.98  sup_bw_superposition:                   708
% 4.08/0.98  sup_immediate_simplified:               1067
% 4.08/0.98  sup_given_eliminated:                   3
% 4.08/0.98  comparisons_done:                       0
% 4.08/0.98  comparisons_avoided:                    0
% 4.08/0.98  
% 4.08/0.98  ------ Simplifications
% 4.08/0.98  
% 4.08/0.98  
% 4.08/0.98  sim_fw_subset_subsumed:                 180
% 4.08/0.98  sim_bw_subset_subsumed:                 26
% 4.08/0.98  sim_fw_subsumed:                        220
% 4.08/0.98  sim_bw_subsumed:                        8
% 4.08/0.98  sim_fw_subsumption_res:                 19
% 4.08/0.98  sim_bw_subsumption_res:                 0
% 4.08/0.98  sim_tautology_del:                      45
% 4.08/0.98  sim_eq_tautology_del:                   115
% 4.08/0.98  sim_eq_res_simp:                        8
% 4.08/0.98  sim_fw_demodulated:                     290
% 4.08/0.98  sim_bw_demodulated:                     19
% 4.08/0.98  sim_light_normalised:                   573
% 4.08/0.98  sim_joinable_taut:                      0
% 4.08/0.98  sim_joinable_simp:                      0
% 4.08/0.98  sim_ac_normalised:                      0
% 4.08/0.98  sim_smt_subsumption:                    0
% 4.08/0.98  
%------------------------------------------------------------------------------

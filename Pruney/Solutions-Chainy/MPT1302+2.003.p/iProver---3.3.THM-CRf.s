%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:22 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 393 expanded)
%              Number of clauses        :   52 ( 112 expanded)
%              Number of leaves         :   12 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  403 (2159 expanded)
%              Number of equality atoms :   83 ( 158 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & v1_tops_2(X1,X0) )
                 => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f27,plain,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
    & v1_tops_2(sK4,sK2)
    & v1_tops_2(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f26,f25,f24])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    v1_tops_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_676,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_677,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_681,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1220,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,sK4) = k2_xboole_0(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_681])).

cnf(c_1238,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_676,c_1220])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_682,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_261,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_262,plain,
    ( v1_tops_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_673,plain,
    ( v1_tops_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_1065,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,X1),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,X1)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_682,c_673])).

cnf(c_1610,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1065])).

cnf(c_1617,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1610,c_1238])).

cnf(c_19,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,negated_conjecture,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_23,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_399,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_416,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_405,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_713,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1113,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
    | ~ v1_tops_2(k2_xboole_0(X0,X1),sK2)
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(X0,X1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1180,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
    | ~ v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
    | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_1181,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | sK2 != sK2
    | v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) = iProver_top
    | v1_tops_2(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1180])).

cnf(c_25933,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1617,c_19,c_20,c_23,c_416,c_1181,c_1238])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_683,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_25937,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_25933,c_683])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(sK1(X0,X1),X0)
    | v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_195,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_196,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_10,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_212,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_196,c_10])).

cnf(c_227,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(sK1(X1,X2),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_17])).

cnf(c_228,plain,
    ( ~ v1_tops_2(X0,sK2)
    | v1_tops_2(X1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK1(sK2,X1),X0) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_1696,plain,
    ( ~ v1_tops_2(X0,sK2)
    | v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_2353,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
    | ~ v1_tops_2(sK3,sK2)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_1696])).

cnf(c_2354,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2353])).

cnf(c_2350,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
    | ~ v1_tops_2(sK4,sK2)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_1696])).

cnf(c_2351,plain,
    ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
    | v1_tops_2(sK4,sK2) != iProver_top
    | m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2350])).

cnf(c_1306,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_682])).

cnf(c_13,negated_conjecture,
    ( v1_tops_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_22,plain,
    ( v1_tops_2(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( v1_tops_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25937,c_2354,c_2351,c_1306,c_1238,c_1181,c_416,c_23,c_22,c_21,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:00:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.21/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/1.48  
% 7.21/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.21/1.48  
% 7.21/1.48  ------  iProver source info
% 7.21/1.48  
% 7.21/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.21/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.21/1.48  git: non_committed_changes: false
% 7.21/1.48  git: last_make_outside_of_git: false
% 7.21/1.48  
% 7.21/1.48  ------ 
% 7.21/1.48  
% 7.21/1.48  ------ Input Options
% 7.21/1.48  
% 7.21/1.48  --out_options                           all
% 7.21/1.48  --tptp_safe_out                         true
% 7.21/1.48  --problem_path                          ""
% 7.21/1.48  --include_path                          ""
% 7.21/1.48  --clausifier                            res/vclausify_rel
% 7.21/1.48  --clausifier_options                    ""
% 7.21/1.48  --stdin                                 false
% 7.21/1.48  --stats_out                             all
% 7.21/1.48  
% 7.21/1.48  ------ General Options
% 7.21/1.48  
% 7.21/1.48  --fof                                   false
% 7.21/1.48  --time_out_real                         305.
% 7.21/1.48  --time_out_virtual                      -1.
% 7.21/1.48  --symbol_type_check                     false
% 7.21/1.48  --clausify_out                          false
% 7.21/1.48  --sig_cnt_out                           false
% 7.21/1.48  --trig_cnt_out                          false
% 7.21/1.48  --trig_cnt_out_tolerance                1.
% 7.21/1.48  --trig_cnt_out_sk_spl                   false
% 7.21/1.48  --abstr_cl_out                          false
% 7.21/1.48  
% 7.21/1.48  ------ Global Options
% 7.21/1.48  
% 7.21/1.48  --schedule                              default
% 7.21/1.48  --add_important_lit                     false
% 7.21/1.48  --prop_solver_per_cl                    1000
% 7.21/1.48  --min_unsat_core                        false
% 7.21/1.48  --soft_assumptions                      false
% 7.21/1.48  --soft_lemma_size                       3
% 7.21/1.48  --prop_impl_unit_size                   0
% 7.21/1.48  --prop_impl_unit                        []
% 7.21/1.48  --share_sel_clauses                     true
% 7.21/1.48  --reset_solvers                         false
% 7.21/1.48  --bc_imp_inh                            [conj_cone]
% 7.21/1.48  --conj_cone_tolerance                   3.
% 7.21/1.48  --extra_neg_conj                        none
% 7.21/1.48  --large_theory_mode                     true
% 7.21/1.48  --prolific_symb_bound                   200
% 7.21/1.48  --lt_threshold                          2000
% 7.21/1.48  --clause_weak_htbl                      true
% 7.21/1.48  --gc_record_bc_elim                     false
% 7.21/1.48  
% 7.21/1.48  ------ Preprocessing Options
% 7.21/1.48  
% 7.21/1.48  --preprocessing_flag                    true
% 7.21/1.48  --time_out_prep_mult                    0.1
% 7.21/1.48  --splitting_mode                        input
% 7.21/1.48  --splitting_grd                         true
% 7.21/1.48  --splitting_cvd                         false
% 7.21/1.48  --splitting_cvd_svl                     false
% 7.21/1.48  --splitting_nvd                         32
% 7.21/1.48  --sub_typing                            true
% 7.21/1.48  --prep_gs_sim                           true
% 7.21/1.48  --prep_unflatten                        true
% 7.21/1.48  --prep_res_sim                          true
% 7.21/1.48  --prep_upred                            true
% 7.21/1.48  --prep_sem_filter                       exhaustive
% 7.21/1.48  --prep_sem_filter_out                   false
% 7.21/1.48  --pred_elim                             true
% 7.21/1.48  --res_sim_input                         true
% 7.21/1.48  --eq_ax_congr_red                       true
% 7.21/1.48  --pure_diseq_elim                       true
% 7.21/1.48  --brand_transform                       false
% 7.21/1.48  --non_eq_to_eq                          false
% 7.21/1.48  --prep_def_merge                        true
% 7.21/1.48  --prep_def_merge_prop_impl              false
% 7.21/1.48  --prep_def_merge_mbd                    true
% 7.21/1.48  --prep_def_merge_tr_red                 false
% 7.21/1.48  --prep_def_merge_tr_cl                  false
% 7.21/1.48  --smt_preprocessing                     true
% 7.21/1.48  --smt_ac_axioms                         fast
% 7.21/1.48  --preprocessed_out                      false
% 7.21/1.48  --preprocessed_stats                    false
% 7.21/1.48  
% 7.21/1.48  ------ Abstraction refinement Options
% 7.21/1.48  
% 7.21/1.48  --abstr_ref                             []
% 7.21/1.48  --abstr_ref_prep                        false
% 7.21/1.48  --abstr_ref_until_sat                   false
% 7.21/1.48  --abstr_ref_sig_restrict                funpre
% 7.21/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.21/1.48  --abstr_ref_under                       []
% 7.21/1.48  
% 7.21/1.48  ------ SAT Options
% 7.21/1.48  
% 7.21/1.48  --sat_mode                              false
% 7.21/1.48  --sat_fm_restart_options                ""
% 7.21/1.48  --sat_gr_def                            false
% 7.21/1.48  --sat_epr_types                         true
% 7.21/1.48  --sat_non_cyclic_types                  false
% 7.21/1.48  --sat_finite_models                     false
% 7.21/1.48  --sat_fm_lemmas                         false
% 7.21/1.48  --sat_fm_prep                           false
% 7.21/1.48  --sat_fm_uc_incr                        true
% 7.21/1.48  --sat_out_model                         small
% 7.21/1.48  --sat_out_clauses                       false
% 7.21/1.48  
% 7.21/1.48  ------ QBF Options
% 7.21/1.48  
% 7.21/1.48  --qbf_mode                              false
% 7.21/1.48  --qbf_elim_univ                         false
% 7.21/1.48  --qbf_dom_inst                          none
% 7.21/1.48  --qbf_dom_pre_inst                      false
% 7.21/1.48  --qbf_sk_in                             false
% 7.21/1.48  --qbf_pred_elim                         true
% 7.21/1.48  --qbf_split                             512
% 7.21/1.48  
% 7.21/1.48  ------ BMC1 Options
% 7.21/1.48  
% 7.21/1.48  --bmc1_incremental                      false
% 7.21/1.48  --bmc1_axioms                           reachable_all
% 7.21/1.48  --bmc1_min_bound                        0
% 7.21/1.48  --bmc1_max_bound                        -1
% 7.21/1.48  --bmc1_max_bound_default                -1
% 7.21/1.48  --bmc1_symbol_reachability              true
% 7.21/1.48  --bmc1_property_lemmas                  false
% 7.21/1.48  --bmc1_k_induction                      false
% 7.21/1.48  --bmc1_non_equiv_states                 false
% 7.21/1.48  --bmc1_deadlock                         false
% 7.21/1.48  --bmc1_ucm                              false
% 7.21/1.48  --bmc1_add_unsat_core                   none
% 7.21/1.48  --bmc1_unsat_core_children              false
% 7.21/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.21/1.48  --bmc1_out_stat                         full
% 7.21/1.48  --bmc1_ground_init                      false
% 7.21/1.48  --bmc1_pre_inst_next_state              false
% 7.21/1.48  --bmc1_pre_inst_state                   false
% 7.21/1.48  --bmc1_pre_inst_reach_state             false
% 7.21/1.48  --bmc1_out_unsat_core                   false
% 7.21/1.48  --bmc1_aig_witness_out                  false
% 7.21/1.48  --bmc1_verbose                          false
% 7.21/1.48  --bmc1_dump_clauses_tptp                false
% 7.21/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.21/1.48  --bmc1_dump_file                        -
% 7.21/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.21/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.21/1.48  --bmc1_ucm_extend_mode                  1
% 7.21/1.48  --bmc1_ucm_init_mode                    2
% 7.21/1.48  --bmc1_ucm_cone_mode                    none
% 7.21/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.21/1.48  --bmc1_ucm_relax_model                  4
% 7.21/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.21/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.21/1.48  --bmc1_ucm_layered_model                none
% 7.21/1.48  --bmc1_ucm_max_lemma_size               10
% 7.21/1.48  
% 7.21/1.48  ------ AIG Options
% 7.21/1.48  
% 7.21/1.48  --aig_mode                              false
% 7.21/1.48  
% 7.21/1.48  ------ Instantiation Options
% 7.21/1.48  
% 7.21/1.48  --instantiation_flag                    true
% 7.21/1.48  --inst_sos_flag                         true
% 7.21/1.48  --inst_sos_phase                        true
% 7.21/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.21/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.21/1.48  --inst_lit_sel_side                     num_symb
% 7.21/1.48  --inst_solver_per_active                1400
% 7.21/1.48  --inst_solver_calls_frac                1.
% 7.21/1.48  --inst_passive_queue_type               priority_queues
% 7.21/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.21/1.48  --inst_passive_queues_freq              [25;2]
% 7.21/1.48  --inst_dismatching                      true
% 7.21/1.48  --inst_eager_unprocessed_to_passive     true
% 7.21/1.48  --inst_prop_sim_given                   true
% 7.21/1.48  --inst_prop_sim_new                     false
% 7.21/1.48  --inst_subs_new                         false
% 7.21/1.48  --inst_eq_res_simp                      false
% 7.21/1.48  --inst_subs_given                       false
% 7.21/1.48  --inst_orphan_elimination               true
% 7.21/1.48  --inst_learning_loop_flag               true
% 7.21/1.48  --inst_learning_start                   3000
% 7.21/1.48  --inst_learning_factor                  2
% 7.21/1.48  --inst_start_prop_sim_after_learn       3
% 7.21/1.48  --inst_sel_renew                        solver
% 7.21/1.48  --inst_lit_activity_flag                true
% 7.21/1.48  --inst_restr_to_given                   false
% 7.21/1.48  --inst_activity_threshold               500
% 7.21/1.48  --inst_out_proof                        true
% 7.21/1.48  
% 7.21/1.48  ------ Resolution Options
% 7.21/1.48  
% 7.21/1.48  --resolution_flag                       true
% 7.21/1.48  --res_lit_sel                           adaptive
% 7.21/1.48  --res_lit_sel_side                      none
% 7.21/1.48  --res_ordering                          kbo
% 7.21/1.48  --res_to_prop_solver                    active
% 7.21/1.48  --res_prop_simpl_new                    false
% 7.21/1.48  --res_prop_simpl_given                  true
% 7.21/1.48  --res_passive_queue_type                priority_queues
% 7.21/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.21/1.48  --res_passive_queues_freq               [15;5]
% 7.21/1.48  --res_forward_subs                      full
% 7.21/1.48  --res_backward_subs                     full
% 7.21/1.48  --res_forward_subs_resolution           true
% 7.21/1.48  --res_backward_subs_resolution          true
% 7.21/1.48  --res_orphan_elimination                true
% 7.21/1.48  --res_time_limit                        2.
% 7.21/1.48  --res_out_proof                         true
% 7.21/1.48  
% 7.21/1.48  ------ Superposition Options
% 7.21/1.48  
% 7.21/1.48  --superposition_flag                    true
% 7.21/1.48  --sup_passive_queue_type                priority_queues
% 7.21/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.21/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.21/1.48  --demod_completeness_check              fast
% 7.21/1.48  --demod_use_ground                      true
% 7.21/1.48  --sup_to_prop_solver                    passive
% 7.21/1.48  --sup_prop_simpl_new                    true
% 7.21/1.48  --sup_prop_simpl_given                  true
% 7.21/1.48  --sup_fun_splitting                     true
% 7.21/1.48  --sup_smt_interval                      50000
% 7.21/1.48  
% 7.21/1.48  ------ Superposition Simplification Setup
% 7.21/1.48  
% 7.21/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.21/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.21/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.21/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.21/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.21/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.21/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.21/1.48  --sup_immed_triv                        [TrivRules]
% 7.21/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.21/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.21/1.48  --sup_immed_bw_main                     []
% 7.21/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.21/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.21/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.21/1.48  --sup_input_bw                          []
% 7.21/1.48  
% 7.21/1.48  ------ Combination Options
% 7.21/1.48  
% 7.21/1.48  --comb_res_mult                         3
% 7.21/1.48  --comb_sup_mult                         2
% 7.21/1.48  --comb_inst_mult                        10
% 7.21/1.48  
% 7.21/1.48  ------ Debug Options
% 7.21/1.48  
% 7.21/1.48  --dbg_backtrace                         false
% 7.21/1.48  --dbg_dump_prop_clauses                 false
% 7.21/1.48  --dbg_dump_prop_clauses_file            -
% 7.21/1.48  --dbg_out_stat                          false
% 7.21/1.48  ------ Parsing...
% 7.21/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.21/1.48  
% 7.21/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.21/1.48  
% 7.21/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.21/1.48  
% 7.21/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.21/1.48  ------ Proving...
% 7.21/1.48  ------ Problem Properties 
% 7.21/1.48  
% 7.21/1.48  
% 7.21/1.48  clauses                                 16
% 7.21/1.48  conjectures                             5
% 7.21/1.48  EPR                                     2
% 7.21/1.48  Horn                                    12
% 7.21/1.48  unary                                   5
% 7.21/1.48  binary                                  2
% 7.21/1.48  lits                                    39
% 7.21/1.48  lits eq                                 4
% 7.21/1.48  fd_pure                                 0
% 7.21/1.48  fd_pseudo                               0
% 7.21/1.48  fd_cond                                 0
% 7.21/1.48  fd_pseudo_cond                          3
% 7.21/1.48  AC symbols                              0
% 7.21/1.48  
% 7.21/1.48  ------ Schedule dynamic 5 is on 
% 7.21/1.48  
% 7.21/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.21/1.48  
% 7.21/1.48  
% 7.21/1.48  ------ 
% 7.21/1.48  Current options:
% 7.21/1.48  ------ 
% 7.21/1.48  
% 7.21/1.48  ------ Input Options
% 7.21/1.48  
% 7.21/1.48  --out_options                           all
% 7.21/1.48  --tptp_safe_out                         true
% 7.21/1.48  --problem_path                          ""
% 7.21/1.48  --include_path                          ""
% 7.21/1.48  --clausifier                            res/vclausify_rel
% 7.21/1.48  --clausifier_options                    ""
% 7.21/1.48  --stdin                                 false
% 7.21/1.48  --stats_out                             all
% 7.21/1.48  
% 7.21/1.48  ------ General Options
% 7.21/1.48  
% 7.21/1.48  --fof                                   false
% 7.21/1.48  --time_out_real                         305.
% 7.21/1.48  --time_out_virtual                      -1.
% 7.21/1.48  --symbol_type_check                     false
% 7.21/1.48  --clausify_out                          false
% 7.21/1.48  --sig_cnt_out                           false
% 7.21/1.48  --trig_cnt_out                          false
% 7.21/1.48  --trig_cnt_out_tolerance                1.
% 7.21/1.48  --trig_cnt_out_sk_spl                   false
% 7.21/1.48  --abstr_cl_out                          false
% 7.21/1.48  
% 7.21/1.48  ------ Global Options
% 7.21/1.48  
% 7.21/1.48  --schedule                              default
% 7.21/1.48  --add_important_lit                     false
% 7.21/1.48  --prop_solver_per_cl                    1000
% 7.21/1.48  --min_unsat_core                        false
% 7.21/1.48  --soft_assumptions                      false
% 7.21/1.48  --soft_lemma_size                       3
% 7.21/1.48  --prop_impl_unit_size                   0
% 7.21/1.48  --prop_impl_unit                        []
% 7.21/1.48  --share_sel_clauses                     true
% 7.21/1.48  --reset_solvers                         false
% 7.21/1.48  --bc_imp_inh                            [conj_cone]
% 7.21/1.48  --conj_cone_tolerance                   3.
% 7.21/1.48  --extra_neg_conj                        none
% 7.21/1.48  --large_theory_mode                     true
% 7.21/1.48  --prolific_symb_bound                   200
% 7.21/1.48  --lt_threshold                          2000
% 7.21/1.48  --clause_weak_htbl                      true
% 7.21/1.48  --gc_record_bc_elim                     false
% 7.21/1.48  
% 7.21/1.48  ------ Preprocessing Options
% 7.21/1.48  
% 7.21/1.48  --preprocessing_flag                    true
% 7.21/1.48  --time_out_prep_mult                    0.1
% 7.21/1.48  --splitting_mode                        input
% 7.21/1.48  --splitting_grd                         true
% 7.21/1.48  --splitting_cvd                         false
% 7.21/1.48  --splitting_cvd_svl                     false
% 7.21/1.48  --splitting_nvd                         32
% 7.21/1.48  --sub_typing                            true
% 7.21/1.48  --prep_gs_sim                           true
% 7.21/1.48  --prep_unflatten                        true
% 7.21/1.48  --prep_res_sim                          true
% 7.21/1.48  --prep_upred                            true
% 7.21/1.48  --prep_sem_filter                       exhaustive
% 7.21/1.48  --prep_sem_filter_out                   false
% 7.21/1.48  --pred_elim                             true
% 7.21/1.48  --res_sim_input                         true
% 7.21/1.48  --eq_ax_congr_red                       true
% 7.21/1.48  --pure_diseq_elim                       true
% 7.21/1.48  --brand_transform                       false
% 7.21/1.48  --non_eq_to_eq                          false
% 7.21/1.48  --prep_def_merge                        true
% 7.21/1.48  --prep_def_merge_prop_impl              false
% 7.21/1.48  --prep_def_merge_mbd                    true
% 7.21/1.48  --prep_def_merge_tr_red                 false
% 7.21/1.48  --prep_def_merge_tr_cl                  false
% 7.21/1.48  --smt_preprocessing                     true
% 7.21/1.48  --smt_ac_axioms                         fast
% 7.21/1.48  --preprocessed_out                      false
% 7.21/1.48  --preprocessed_stats                    false
% 7.21/1.48  
% 7.21/1.48  ------ Abstraction refinement Options
% 7.21/1.48  
% 7.21/1.48  --abstr_ref                             []
% 7.21/1.48  --abstr_ref_prep                        false
% 7.21/1.48  --abstr_ref_until_sat                   false
% 7.21/1.48  --abstr_ref_sig_restrict                funpre
% 7.21/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.21/1.48  --abstr_ref_under                       []
% 7.21/1.48  
% 7.21/1.48  ------ SAT Options
% 7.21/1.48  
% 7.21/1.48  --sat_mode                              false
% 7.21/1.48  --sat_fm_restart_options                ""
% 7.21/1.48  --sat_gr_def                            false
% 7.21/1.48  --sat_epr_types                         true
% 7.21/1.48  --sat_non_cyclic_types                  false
% 7.21/1.48  --sat_finite_models                     false
% 7.21/1.48  --sat_fm_lemmas                         false
% 7.21/1.48  --sat_fm_prep                           false
% 7.21/1.48  --sat_fm_uc_incr                        true
% 7.21/1.48  --sat_out_model                         small
% 7.21/1.48  --sat_out_clauses                       false
% 7.21/1.48  
% 7.21/1.48  ------ QBF Options
% 7.21/1.48  
% 7.21/1.48  --qbf_mode                              false
% 7.21/1.48  --qbf_elim_univ                         false
% 7.21/1.48  --qbf_dom_inst                          none
% 7.21/1.48  --qbf_dom_pre_inst                      false
% 7.21/1.48  --qbf_sk_in                             false
% 7.21/1.48  --qbf_pred_elim                         true
% 7.21/1.48  --qbf_split                             512
% 7.21/1.48  
% 7.21/1.48  ------ BMC1 Options
% 7.21/1.48  
% 7.21/1.48  --bmc1_incremental                      false
% 7.21/1.48  --bmc1_axioms                           reachable_all
% 7.21/1.48  --bmc1_min_bound                        0
% 7.21/1.48  --bmc1_max_bound                        -1
% 7.21/1.48  --bmc1_max_bound_default                -1
% 7.21/1.48  --bmc1_symbol_reachability              true
% 7.21/1.48  --bmc1_property_lemmas                  false
% 7.21/1.48  --bmc1_k_induction                      false
% 7.21/1.48  --bmc1_non_equiv_states                 false
% 7.21/1.48  --bmc1_deadlock                         false
% 7.21/1.48  --bmc1_ucm                              false
% 7.21/1.48  --bmc1_add_unsat_core                   none
% 7.21/1.48  --bmc1_unsat_core_children              false
% 7.21/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.21/1.48  --bmc1_out_stat                         full
% 7.21/1.48  --bmc1_ground_init                      false
% 7.21/1.48  --bmc1_pre_inst_next_state              false
% 7.21/1.48  --bmc1_pre_inst_state                   false
% 7.21/1.48  --bmc1_pre_inst_reach_state             false
% 7.21/1.48  --bmc1_out_unsat_core                   false
% 7.21/1.48  --bmc1_aig_witness_out                  false
% 7.21/1.48  --bmc1_verbose                          false
% 7.21/1.48  --bmc1_dump_clauses_tptp                false
% 7.21/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.21/1.48  --bmc1_dump_file                        -
% 7.21/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.21/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.21/1.48  --bmc1_ucm_extend_mode                  1
% 7.21/1.48  --bmc1_ucm_init_mode                    2
% 7.21/1.48  --bmc1_ucm_cone_mode                    none
% 7.21/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.21/1.48  --bmc1_ucm_relax_model                  4
% 7.21/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.21/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.21/1.48  --bmc1_ucm_layered_model                none
% 7.21/1.48  --bmc1_ucm_max_lemma_size               10
% 7.21/1.48  
% 7.21/1.48  ------ AIG Options
% 7.21/1.48  
% 7.21/1.48  --aig_mode                              false
% 7.21/1.48  
% 7.21/1.48  ------ Instantiation Options
% 7.21/1.48  
% 7.21/1.48  --instantiation_flag                    true
% 7.21/1.48  --inst_sos_flag                         true
% 7.21/1.48  --inst_sos_phase                        true
% 7.21/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.21/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.21/1.48  --inst_lit_sel_side                     none
% 7.21/1.48  --inst_solver_per_active                1400
% 7.21/1.48  --inst_solver_calls_frac                1.
% 7.21/1.48  --inst_passive_queue_type               priority_queues
% 7.21/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.21/1.48  --inst_passive_queues_freq              [25;2]
% 7.21/1.48  --inst_dismatching                      true
% 7.21/1.48  --inst_eager_unprocessed_to_passive     true
% 7.21/1.48  --inst_prop_sim_given                   true
% 7.21/1.48  --inst_prop_sim_new                     false
% 7.21/1.48  --inst_subs_new                         false
% 7.21/1.48  --inst_eq_res_simp                      false
% 7.21/1.48  --inst_subs_given                       false
% 7.21/1.48  --inst_orphan_elimination               true
% 7.21/1.48  --inst_learning_loop_flag               true
% 7.21/1.48  --inst_learning_start                   3000
% 7.21/1.48  --inst_learning_factor                  2
% 7.21/1.48  --inst_start_prop_sim_after_learn       3
% 7.21/1.48  --inst_sel_renew                        solver
% 7.21/1.48  --inst_lit_activity_flag                true
% 7.21/1.48  --inst_restr_to_given                   false
% 7.21/1.48  --inst_activity_threshold               500
% 7.21/1.48  --inst_out_proof                        true
% 7.21/1.48  
% 7.21/1.48  ------ Resolution Options
% 7.21/1.48  
% 7.21/1.48  --resolution_flag                       false
% 7.21/1.48  --res_lit_sel                           adaptive
% 7.21/1.48  --res_lit_sel_side                      none
% 7.21/1.48  --res_ordering                          kbo
% 7.21/1.48  --res_to_prop_solver                    active
% 7.21/1.48  --res_prop_simpl_new                    false
% 7.21/1.48  --res_prop_simpl_given                  true
% 7.21/1.48  --res_passive_queue_type                priority_queues
% 7.21/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.21/1.48  --res_passive_queues_freq               [15;5]
% 7.21/1.48  --res_forward_subs                      full
% 7.21/1.48  --res_backward_subs                     full
% 7.21/1.48  --res_forward_subs_resolution           true
% 7.21/1.48  --res_backward_subs_resolution          true
% 7.21/1.48  --res_orphan_elimination                true
% 7.21/1.48  --res_time_limit                        2.
% 7.21/1.48  --res_out_proof                         true
% 7.21/1.48  
% 7.21/1.48  ------ Superposition Options
% 7.21/1.48  
% 7.21/1.48  --superposition_flag                    true
% 7.21/1.48  --sup_passive_queue_type                priority_queues
% 7.21/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.21/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.21/1.48  --demod_completeness_check              fast
% 7.21/1.48  --demod_use_ground                      true
% 7.21/1.48  --sup_to_prop_solver                    passive
% 7.21/1.48  --sup_prop_simpl_new                    true
% 7.21/1.48  --sup_prop_simpl_given                  true
% 7.21/1.48  --sup_fun_splitting                     true
% 7.21/1.48  --sup_smt_interval                      50000
% 7.21/1.48  
% 7.21/1.48  ------ Superposition Simplification Setup
% 7.21/1.48  
% 7.21/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.21/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.21/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.21/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.21/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.21/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.21/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.21/1.48  --sup_immed_triv                        [TrivRules]
% 7.21/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.21/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.21/1.48  --sup_immed_bw_main                     []
% 7.21/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.21/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.21/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.21/1.48  --sup_input_bw                          []
% 7.21/1.48  
% 7.21/1.48  ------ Combination Options
% 7.21/1.48  
% 7.21/1.48  --comb_res_mult                         3
% 7.21/1.48  --comb_sup_mult                         2
% 7.21/1.48  --comb_inst_mult                        10
% 7.21/1.48  
% 7.21/1.48  ------ Debug Options
% 7.21/1.48  
% 7.21/1.48  --dbg_backtrace                         false
% 7.21/1.48  --dbg_dump_prop_clauses                 false
% 7.21/1.48  --dbg_dump_prop_clauses_file            -
% 7.21/1.48  --dbg_out_stat                          false
% 7.21/1.48  
% 7.21/1.48  
% 7.21/1.48  
% 7.21/1.48  
% 7.21/1.48  ------ Proving...
% 7.21/1.48  
% 7.21/1.48  
% 7.21/1.48  % SZS status Theorem for theBenchmark.p
% 7.21/1.48  
% 7.21/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.21/1.48  
% 7.21/1.48  fof(f5,conjecture,(
% 7.21/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 7.21/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.21/1.48  
% 7.21/1.48  fof(f6,negated_conjecture,(
% 7.21/1.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 7.21/1.48    inference(negated_conjecture,[],[f5])).
% 7.21/1.48  
% 7.21/1.48  fof(f13,plain,(
% 7.21/1.48    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v1_tops_2(X2,X0) & v1_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 7.21/1.48    inference(ennf_transformation,[],[f6])).
% 7.21/1.48  
% 7.21/1.48  fof(f14,plain,(
% 7.21/1.48    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 7.21/1.48    inference(flattening,[],[f13])).
% 7.21/1.48  
% 7.21/1.48  fof(f26,plain,(
% 7.21/1.48    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK4),X0) & v1_tops_2(sK4,X0) & v1_tops_2(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.21/1.48    introduced(choice_axiom,[])).
% 7.21/1.48  
% 7.21/1.48  fof(f25,plain,(
% 7.21/1.48    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK3,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(sK3,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.21/1.48    introduced(choice_axiom,[])).
% 7.21/1.48  
% 7.21/1.48  fof(f24,plain,(
% 7.21/1.48    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X1,X2),sK2) & v1_tops_2(X2,sK2) & v1_tops_2(X1,sK2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 7.21/1.48    introduced(choice_axiom,[])).
% 7.21/1.48  
% 7.21/1.48  fof(f27,plain,(
% 7.21/1.48    ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) & v1_tops_2(sK4,sK2) & v1_tops_2(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 7.21/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f26,f25,f24])).
% 7.21/1.48  
% 7.21/1.48  fof(f41,plain,(
% 7.21/1.48    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 7.21/1.48    inference(cnf_transformation,[],[f27])).
% 7.21/1.48  
% 7.21/1.48  fof(f42,plain,(
% 7.21/1.48    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 7.21/1.48    inference(cnf_transformation,[],[f27])).
% 7.21/1.48  
% 7.21/1.48  fof(f3,axiom,(
% 7.21/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.21/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.21/1.48  
% 7.21/1.48  fof(f9,plain,(
% 7.21/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.21/1.48    inference(ennf_transformation,[],[f3])).
% 7.21/1.48  
% 7.21/1.48  fof(f10,plain,(
% 7.21/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.21/1.48    inference(flattening,[],[f9])).
% 7.21/1.48  
% 7.21/1.48  fof(f35,plain,(
% 7.21/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.21/1.48    inference(cnf_transformation,[],[f10])).
% 7.21/1.48  
% 7.21/1.48  fof(f2,axiom,(
% 7.21/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.21/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.21/1.48  
% 7.21/1.48  fof(f7,plain,(
% 7.21/1.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.21/1.48    inference(ennf_transformation,[],[f2])).
% 7.21/1.48  
% 7.21/1.48  fof(f8,plain,(
% 7.21/1.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.21/1.48    inference(flattening,[],[f7])).
% 7.21/1.48  
% 7.21/1.48  fof(f34,plain,(
% 7.21/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.21/1.48    inference(cnf_transformation,[],[f8])).
% 7.21/1.48  
% 7.21/1.48  fof(f4,axiom,(
% 7.21/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 7.21/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.21/1.48  
% 7.21/1.48  fof(f11,plain,(
% 7.21/1.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.21/1.48    inference(ennf_transformation,[],[f4])).
% 7.21/1.48  
% 7.21/1.48  fof(f12,plain,(
% 7.21/1.48    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.21/1.48    inference(flattening,[],[f11])).
% 7.21/1.48  
% 7.21/1.48  fof(f20,plain,(
% 7.21/1.48    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.21/1.48    inference(nnf_transformation,[],[f12])).
% 7.21/1.48  
% 7.21/1.48  fof(f21,plain,(
% 7.21/1.48    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.21/1.48    inference(rectify,[],[f20])).
% 7.21/1.48  
% 7.21/1.48  fof(f22,plain,(
% 7.21/1.48    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.21/1.48    introduced(choice_axiom,[])).
% 7.21/1.48  
% 7.21/1.48  fof(f23,plain,(
% 7.21/1.48    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.21/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 7.21/1.48  
% 7.21/1.48  fof(f38,plain,(
% 7.21/1.48    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.21/1.48    inference(cnf_transformation,[],[f23])).
% 7.21/1.48  
% 7.21/1.48  fof(f40,plain,(
% 7.21/1.48    l1_pre_topc(sK2)),
% 7.21/1.48    inference(cnf_transformation,[],[f27])).
% 7.21/1.48  
% 7.21/1.48  fof(f45,plain,(
% 7.21/1.48    ~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)),
% 7.21/1.48    inference(cnf_transformation,[],[f27])).
% 7.21/1.48  
% 7.21/1.48  fof(f1,axiom,(
% 7.21/1.48    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.21/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.21/1.48  
% 7.21/1.48  fof(f15,plain,(
% 7.21/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.21/1.48    inference(nnf_transformation,[],[f1])).
% 7.21/1.48  
% 7.21/1.48  fof(f16,plain,(
% 7.21/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.21/1.48    inference(flattening,[],[f15])).
% 7.21/1.48  
% 7.21/1.48  fof(f17,plain,(
% 7.21/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.21/1.48    inference(rectify,[],[f16])).
% 7.21/1.48  
% 7.21/1.48  fof(f18,plain,(
% 7.21/1.48    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.21/1.48    introduced(choice_axiom,[])).
% 7.21/1.48  
% 7.21/1.48  fof(f19,plain,(
% 7.21/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.21/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 7.21/1.48  
% 7.21/1.48  fof(f28,plain,(
% 7.21/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 7.21/1.48    inference(cnf_transformation,[],[f19])).
% 7.21/1.48  
% 7.21/1.48  fof(f48,plain,(
% 7.21/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 7.21/1.48    inference(equality_resolution,[],[f28])).
% 7.21/1.48  
% 7.21/1.48  fof(f39,plain,(
% 7.21/1.48    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.21/1.48    inference(cnf_transformation,[],[f23])).
% 7.21/1.48  
% 7.21/1.48  fof(f36,plain,(
% 7.21/1.48    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.21/1.48    inference(cnf_transformation,[],[f23])).
% 7.21/1.48  
% 7.21/1.48  fof(f37,plain,(
% 7.21/1.48    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.21/1.48    inference(cnf_transformation,[],[f23])).
% 7.21/1.48  
% 7.21/1.48  fof(f44,plain,(
% 7.21/1.48    v1_tops_2(sK4,sK2)),
% 7.21/1.48    inference(cnf_transformation,[],[f27])).
% 7.21/1.48  
% 7.21/1.48  fof(f43,plain,(
% 7.21/1.48    v1_tops_2(sK3,sK2)),
% 7.21/1.48    inference(cnf_transformation,[],[f27])).
% 7.21/1.48  
% 7.21/1.48  cnf(c_16,negated_conjecture,
% 7.21/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 7.21/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_676,plain,
% 7.21/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_15,negated_conjecture,
% 7.21/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 7.21/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_677,plain,
% 7.21/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_7,plain,
% 7.21/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.21/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.21/1.48      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 7.21/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_681,plain,
% 7.21/1.48      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 7.21/1.48      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.21/1.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1220,plain,
% 7.21/1.48      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,sK4) = k2_xboole_0(X0,sK4)
% 7.21/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 7.21/1.48      inference(superposition,[status(thm)],[c_677,c_681]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1238,plain,
% 7.21/1.48      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 7.21/1.48      inference(superposition,[status(thm)],[c_676,c_1220]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_6,plain,
% 7.21/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.21/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.21/1.48      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.21/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_682,plain,
% 7.21/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.21/1.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.21/1.48      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_9,plain,
% 7.21/1.48      ( v1_tops_2(X0,X1)
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | r2_hidden(sK1(X1,X0),X0)
% 7.21/1.48      | ~ l1_pre_topc(X1) ),
% 7.21/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_17,negated_conjecture,
% 7.21/1.48      ( l1_pre_topc(sK2) ),
% 7.21/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_261,plain,
% 7.21/1.48      ( v1_tops_2(X0,X1)
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | r2_hidden(sK1(X1,X0),X0)
% 7.21/1.48      | sK2 != X1 ),
% 7.21/1.48      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_262,plain,
% 7.21/1.48      ( v1_tops_2(X0,sK2)
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | r2_hidden(sK1(sK2,X0),X0) ),
% 7.21/1.48      inference(unflattening,[status(thm)],[c_261]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_673,plain,
% 7.21/1.48      ( v1_tops_2(X0,sK2) = iProver_top
% 7.21/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | r2_hidden(sK1(sK2,X0),X0) = iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1065,plain,
% 7.21/1.48      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,X1),sK2) = iProver_top
% 7.21/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | r2_hidden(sK1(sK2,k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,X1)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),X0,X1)) = iProver_top ),
% 7.21/1.48      inference(superposition,[status(thm)],[c_682,c_673]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1610,plain,
% 7.21/1.48      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) = iProver_top
% 7.21/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) = iProver_top ),
% 7.21/1.48      inference(superposition,[status(thm)],[c_1238,c_1065]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1617,plain,
% 7.21/1.48      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
% 7.21/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) = iProver_top ),
% 7.21/1.48      inference(light_normalisation,[status(thm)],[c_1610,c_1238]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_19,plain,
% 7.21/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_20,plain,
% 7.21/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_12,negated_conjecture,
% 7.21/1.48      ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) ),
% 7.21/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_23,plain,
% 7.21/1.48      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) != iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_399,plain,( X0 = X0 ),theory(equality) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_416,plain,
% 7.21/1.48      ( sK2 = sK2 ),
% 7.21/1.48      inference(instantiation,[status(thm)],[c_399]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_405,plain,
% 7.21/1.48      ( ~ v1_tops_2(X0,X1) | v1_tops_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.21/1.48      theory(equality) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_713,plain,
% 7.21/1.48      ( ~ v1_tops_2(X0,X1)
% 7.21/1.48      | v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
% 7.21/1.48      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != X0
% 7.21/1.48      | sK2 != X1 ),
% 7.21/1.48      inference(instantiation,[status(thm)],[c_405]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1113,plain,
% 7.21/1.48      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
% 7.21/1.48      | ~ v1_tops_2(k2_xboole_0(X0,X1),sK2)
% 7.21/1.48      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(X0,X1)
% 7.21/1.48      | sK2 != sK2 ),
% 7.21/1.48      inference(instantiation,[status(thm)],[c_713]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1180,plain,
% 7.21/1.48      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2)
% 7.21/1.48      | ~ v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
% 7.21/1.48      | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 7.21/1.48      | sK2 != sK2 ),
% 7.21/1.48      inference(instantiation,[status(thm)],[c_1113]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1181,plain,
% 7.21/1.48      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 7.21/1.48      | sK2 != sK2
% 7.21/1.48      | v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),sK3,sK4),sK2) = iProver_top
% 7.21/1.48      | v1_tops_2(k2_xboole_0(sK3,sK4),sK2) != iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_1180]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_25933,plain,
% 7.21/1.48      ( r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) = iProver_top ),
% 7.21/1.48      inference(global_propositional_subsumption,
% 7.21/1.48                [status(thm)],
% 7.21/1.48                [c_1617,c_19,c_20,c_23,c_416,c_1181,c_1238]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_5,plain,
% 7.21/1.48      ( r2_hidden(X0,X1)
% 7.21/1.48      | r2_hidden(X0,X2)
% 7.21/1.48      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 7.21/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_683,plain,
% 7.21/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.21/1.48      | r2_hidden(X0,X2) = iProver_top
% 7.21/1.48      | r2_hidden(X0,k2_xboole_0(X1,X2)) != iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_25937,plain,
% 7.21/1.48      ( r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4) = iProver_top
% 7.21/1.48      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) = iProver_top ),
% 7.21/1.48      inference(superposition,[status(thm)],[c_25933,c_683]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_8,plain,
% 7.21/1.48      ( ~ v3_pre_topc(sK1(X0,X1),X0)
% 7.21/1.48      | v1_tops_2(X1,X0)
% 7.21/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.21/1.48      | ~ l1_pre_topc(X0) ),
% 7.21/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_11,plain,
% 7.21/1.48      ( v3_pre_topc(X0,X1)
% 7.21/1.48      | ~ v1_tops_2(X2,X1)
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.21/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | ~ r2_hidden(X0,X2)
% 7.21/1.48      | ~ l1_pre_topc(X1) ),
% 7.21/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_195,plain,
% 7.21/1.48      ( ~ v1_tops_2(X0,X1)
% 7.21/1.48      | v1_tops_2(X2,X3)
% 7.21/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 7.21/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | ~ r2_hidden(X4,X0)
% 7.21/1.48      | ~ l1_pre_topc(X3)
% 7.21/1.48      | ~ l1_pre_topc(X1)
% 7.21/1.48      | X1 != X3
% 7.21/1.48      | sK1(X3,X2) != X4 ),
% 7.21/1.48      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_196,plain,
% 7.21/1.48      ( ~ v1_tops_2(X0,X1)
% 7.21/1.48      | v1_tops_2(X2,X1)
% 7.21/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | ~ m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 7.21/1.48      | ~ r2_hidden(sK1(X1,X2),X0)
% 7.21/1.48      | ~ l1_pre_topc(X1) ),
% 7.21/1.48      inference(unflattening,[status(thm)],[c_195]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_10,plain,
% 7.21/1.48      ( v1_tops_2(X0,X1)
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.21/1.48      | ~ l1_pre_topc(X1) ),
% 7.21/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_212,plain,
% 7.21/1.48      ( ~ v1_tops_2(X0,X1)
% 7.21/1.48      | v1_tops_2(X2,X1)
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | ~ r2_hidden(sK1(X1,X2),X0)
% 7.21/1.48      | ~ l1_pre_topc(X1) ),
% 7.21/1.48      inference(forward_subsumption_resolution,
% 7.21/1.48                [status(thm)],
% 7.21/1.48                [c_196,c_10]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_227,plain,
% 7.21/1.48      ( ~ v1_tops_2(X0,X1)
% 7.21/1.48      | v1_tops_2(X2,X1)
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.21/1.48      | ~ r2_hidden(sK1(X1,X2),X0)
% 7.21/1.48      | sK2 != X1 ),
% 7.21/1.48      inference(resolution_lifted,[status(thm)],[c_212,c_17]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_228,plain,
% 7.21/1.48      ( ~ v1_tops_2(X0,sK2)
% 7.21/1.48      | v1_tops_2(X1,sK2)
% 7.21/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | ~ r2_hidden(sK1(sK2,X1),X0) ),
% 7.21/1.48      inference(unflattening,[status(thm)],[c_227]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1696,plain,
% 7.21/1.48      ( ~ v1_tops_2(X0,sK2)
% 7.21/1.48      | v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
% 7.21/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),X0) ),
% 7.21/1.48      inference(instantiation,[status(thm)],[c_228]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_2353,plain,
% 7.21/1.48      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
% 7.21/1.48      | ~ v1_tops_2(sK3,sK2)
% 7.21/1.48      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) ),
% 7.21/1.48      inference(instantiation,[status(thm)],[c_1696]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_2354,plain,
% 7.21/1.48      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
% 7.21/1.48      | v1_tops_2(sK3,sK2) != iProver_top
% 7.21/1.48      | m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) != iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_2353]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_2350,plain,
% 7.21/1.48      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2)
% 7.21/1.48      | ~ v1_tops_2(sK4,sK2)
% 7.21/1.48      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.21/1.48      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4) ),
% 7.21/1.48      inference(instantiation,[status(thm)],[c_1696]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_2351,plain,
% 7.21/1.48      ( v1_tops_2(k2_xboole_0(sK3,sK4),sK2) = iProver_top
% 7.21/1.48      | v1_tops_2(sK4,sK2) != iProver_top
% 7.21/1.48      | m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4) != iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_2350]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_1306,plain,
% 7.21/1.48      ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.21/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.21/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 7.21/1.48      inference(superposition,[status(thm)],[c_1238,c_682]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_13,negated_conjecture,
% 7.21/1.48      ( v1_tops_2(sK4,sK2) ),
% 7.21/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_22,plain,
% 7.21/1.48      ( v1_tops_2(sK4,sK2) = iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_14,negated_conjecture,
% 7.21/1.48      ( v1_tops_2(sK3,sK2) ),
% 7.21/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(c_21,plain,
% 7.21/1.48      ( v1_tops_2(sK3,sK2) = iProver_top ),
% 7.21/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.21/1.48  
% 7.21/1.48  cnf(contradiction,plain,
% 7.21/1.48      ( $false ),
% 7.21/1.48      inference(minisat,
% 7.21/1.48                [status(thm)],
% 7.21/1.48                [c_25937,c_2354,c_2351,c_1306,c_1238,c_1181,c_416,c_23,
% 7.21/1.48                 c_22,c_21,c_20,c_19]) ).
% 7.21/1.48  
% 7.21/1.48  
% 7.21/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.21/1.48  
% 7.21/1.48  ------                               Statistics
% 7.21/1.48  
% 7.21/1.48  ------ General
% 7.21/1.48  
% 7.21/1.48  abstr_ref_over_cycles:                  0
% 7.21/1.48  abstr_ref_under_cycles:                 0
% 7.21/1.48  gc_basic_clause_elim:                   0
% 7.21/1.48  forced_gc_time:                         0
% 7.21/1.48  parsing_time:                           0.008
% 7.21/1.48  unif_index_cands_time:                  0.
% 7.21/1.48  unif_index_add_time:                    0.
% 7.21/1.48  orderings_time:                         0.
% 7.21/1.48  out_proof_time:                         0.011
% 7.21/1.48  total_time:                             0.862
% 7.21/1.48  num_of_symbols:                         45
% 7.21/1.48  num_of_terms:                           31323
% 7.21/1.48  
% 7.21/1.48  ------ Preprocessing
% 7.21/1.48  
% 7.21/1.48  num_of_splits:                          0
% 7.21/1.48  num_of_split_atoms:                     0
% 7.21/1.48  num_of_reused_defs:                     0
% 7.21/1.48  num_eq_ax_congr_red:                    20
% 7.21/1.48  num_of_sem_filtered_clauses:            1
% 7.21/1.48  num_of_subtypes:                        0
% 7.21/1.48  monotx_restored_types:                  0
% 7.21/1.48  sat_num_of_epr_types:                   0
% 7.21/1.48  sat_num_of_non_cyclic_types:            0
% 7.21/1.48  sat_guarded_non_collapsed_types:        0
% 7.21/1.48  num_pure_diseq_elim:                    0
% 7.21/1.48  simp_replaced_by:                       0
% 7.21/1.48  res_preprocessed:                       85
% 7.21/1.48  prep_upred:                             0
% 7.21/1.48  prep_unflattend:                        5
% 7.21/1.48  smt_new_axioms:                         0
% 7.21/1.48  pred_elim_cands:                        3
% 7.21/1.48  pred_elim:                              2
% 7.21/1.48  pred_elim_cl:                           2
% 7.21/1.48  pred_elim_cycles:                       4
% 7.21/1.48  merged_defs:                            0
% 7.21/1.48  merged_defs_ncl:                        0
% 7.21/1.48  bin_hyper_res:                          0
% 7.21/1.48  prep_cycles:                            4
% 7.21/1.48  pred_elim_time:                         0.002
% 7.21/1.48  splitting_time:                         0.
% 7.21/1.48  sem_filter_time:                        0.
% 7.21/1.48  monotx_time:                            0.
% 7.21/1.48  subtype_inf_time:                       0.
% 7.21/1.48  
% 7.21/1.48  ------ Problem properties
% 7.21/1.48  
% 7.21/1.48  clauses:                                16
% 7.21/1.49  conjectures:                            5
% 7.21/1.49  epr:                                    2
% 7.21/1.49  horn:                                   12
% 7.21/1.49  ground:                                 5
% 7.21/1.49  unary:                                  5
% 7.21/1.49  binary:                                 2
% 7.21/1.49  lits:                                   39
% 7.21/1.49  lits_eq:                                4
% 7.21/1.49  fd_pure:                                0
% 7.21/1.49  fd_pseudo:                              0
% 7.21/1.49  fd_cond:                                0
% 7.21/1.49  fd_pseudo_cond:                         3
% 7.21/1.49  ac_symbols:                             0
% 7.21/1.49  
% 7.21/1.49  ------ Propositional Solver
% 7.21/1.49  
% 7.21/1.49  prop_solver_calls:                      35
% 7.21/1.49  prop_fast_solver_calls:                 766
% 7.21/1.49  smt_solver_calls:                       0
% 7.21/1.49  smt_fast_solver_calls:                  0
% 7.21/1.49  prop_num_of_clauses:                    11487
% 7.21/1.49  prop_preprocess_simplified:             21104
% 7.21/1.49  prop_fo_subsumed:                       36
% 7.21/1.49  prop_solver_time:                       0.
% 7.21/1.49  smt_solver_time:                        0.
% 7.21/1.49  smt_fast_solver_time:                   0.
% 7.21/1.49  prop_fast_solver_time:                  0.
% 7.21/1.49  prop_unsat_core_time:                   0.001
% 7.21/1.49  
% 7.21/1.49  ------ QBF
% 7.21/1.49  
% 7.21/1.49  qbf_q_res:                              0
% 7.21/1.49  qbf_num_tautologies:                    0
% 7.21/1.49  qbf_prep_cycles:                        0
% 7.21/1.49  
% 7.21/1.49  ------ BMC1
% 7.21/1.49  
% 7.21/1.49  bmc1_current_bound:                     -1
% 7.21/1.49  bmc1_last_solved_bound:                 -1
% 7.21/1.49  bmc1_unsat_core_size:                   -1
% 7.21/1.49  bmc1_unsat_core_parents_size:           -1
% 7.21/1.49  bmc1_merge_next_fun:                    0
% 7.21/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.21/1.49  
% 7.21/1.49  ------ Instantiation
% 7.21/1.49  
% 7.21/1.49  inst_num_of_clauses:                    3660
% 7.21/1.49  inst_num_in_passive:                    2238
% 7.21/1.49  inst_num_in_active:                     738
% 7.21/1.49  inst_num_in_unprocessed:                684
% 7.21/1.49  inst_num_of_loops:                      810
% 7.21/1.49  inst_num_of_learning_restarts:          0
% 7.21/1.49  inst_num_moves_active_passive:          68
% 7.21/1.49  inst_lit_activity:                      0
% 7.21/1.49  inst_lit_activity_moves:                2
% 7.21/1.49  inst_num_tautologies:                   0
% 7.21/1.49  inst_num_prop_implied:                  0
% 7.21/1.49  inst_num_existing_simplified:           0
% 7.21/1.49  inst_num_eq_res_simplified:             0
% 7.21/1.49  inst_num_child_elim:                    0
% 7.21/1.49  inst_num_of_dismatching_blockings:      5801
% 7.21/1.49  inst_num_of_non_proper_insts:           3522
% 7.21/1.49  inst_num_of_duplicates:                 0
% 7.21/1.49  inst_inst_num_from_inst_to_res:         0
% 7.21/1.49  inst_dismatching_checking_time:         0.
% 7.21/1.49  
% 7.21/1.49  ------ Resolution
% 7.21/1.49  
% 7.21/1.49  res_num_of_clauses:                     0
% 7.21/1.49  res_num_in_passive:                     0
% 7.21/1.49  res_num_in_active:                      0
% 7.21/1.49  res_num_of_loops:                       89
% 7.21/1.49  res_forward_subset_subsumed:            59
% 7.21/1.49  res_backward_subset_subsumed:           0
% 7.21/1.49  res_forward_subsumed:                   0
% 7.21/1.49  res_backward_subsumed:                  0
% 7.21/1.49  res_forward_subsumption_resolution:     1
% 7.21/1.49  res_backward_subsumption_resolution:    0
% 7.21/1.49  res_clause_to_clause_subsumption:       2174
% 7.21/1.49  res_orphan_elimination:                 0
% 7.21/1.49  res_tautology_del:                      15
% 7.21/1.49  res_num_eq_res_simplified:              0
% 7.21/1.49  res_num_sel_changes:                    0
% 7.21/1.49  res_moves_from_active_to_pass:          0
% 7.21/1.49  
% 7.21/1.49  ------ Superposition
% 7.21/1.49  
% 7.21/1.49  sup_time_total:                         0.
% 7.21/1.49  sup_time_generating:                    0.
% 7.21/1.49  sup_time_sim_full:                      0.
% 7.21/1.49  sup_time_sim_immed:                     0.
% 7.21/1.49  
% 7.21/1.49  sup_num_of_clauses:                     1001
% 7.21/1.49  sup_num_in_active:                      158
% 7.21/1.49  sup_num_in_passive:                     843
% 7.21/1.49  sup_num_of_loops:                       161
% 7.21/1.49  sup_fw_superposition:                   439
% 7.21/1.49  sup_bw_superposition:                   681
% 7.21/1.49  sup_immediate_simplified:               266
% 7.21/1.49  sup_given_eliminated:                   0
% 7.21/1.49  comparisons_done:                       0
% 7.21/1.49  comparisons_avoided:                    0
% 7.21/1.49  
% 7.21/1.49  ------ Simplifications
% 7.21/1.49  
% 7.21/1.49  
% 7.21/1.49  sim_fw_subset_subsumed:                 9
% 7.21/1.49  sim_bw_subset_subsumed:                 3
% 7.21/1.49  sim_fw_subsumed:                        8
% 7.21/1.49  sim_bw_subsumed:                        1
% 7.21/1.49  sim_fw_subsumption_res:                 0
% 7.21/1.49  sim_bw_subsumption_res:                 0
% 7.21/1.49  sim_tautology_del:                      11
% 7.21/1.49  sim_eq_tautology_del:                   8
% 7.21/1.49  sim_eq_res_simp:                        6
% 7.21/1.49  sim_fw_demodulated:                     22
% 7.21/1.49  sim_bw_demodulated:                     1
% 7.21/1.49  sim_light_normalised:                   230
% 7.21/1.49  sim_joinable_taut:                      0
% 7.21/1.49  sim_joinable_simp:                      0
% 7.21/1.49  sim_ac_normalised:                      0
% 7.21/1.49  sim_smt_subsumption:                    0
% 7.21/1.49  
%------------------------------------------------------------------------------

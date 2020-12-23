%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:08 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  162 (1208 expanded)
%              Number of clauses        :  108 ( 348 expanded)
%              Number of leaves         :   15 ( 289 expanded)
%              Depth                    :   31
%              Number of atoms          :  627 (9914 expanded)
%              Number of equality atoms :  196 (1757 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,X0)
        & r1_tarski(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,X0)
              & r1_tarski(X2,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tops_1(sK1,X0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,X0)
              | ~ r1_tarski(X3,sK1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1753,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1760,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_18,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1754,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2356,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1754])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_288,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_289,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_20])).

cnf(c_294,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_1918,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_1919,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1918])).

cnf(c_12,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_404,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_405,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_1921,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1922,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1921])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_1924,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_1925,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_1963,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1964,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1963])).

cnf(c_1243,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2113,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2004,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2174,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_2175,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2174])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2015,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2300,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_2482,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_2483,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2482])).

cnf(c_1940,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3125,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1940])).

cnf(c_3126,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3125])).

cnf(c_1244,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1991,plain,
    ( k1_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_3485,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_3734,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2356,c_24,c_1919,c_1922,c_1925,c_1964,c_2113,c_2175,c_2483,c_3126,c_3485])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1755,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_331,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_332,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_336,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_20])).

cnf(c_337,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_336])).

cnf(c_371,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_337,c_20])).

cnf(c_372,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1240,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_372])).

cnf(c_1750,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_1241,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_372])).

cnf(c_1270,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_1271,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_10,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_306,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_307,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_311,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_20])).

cnf(c_312,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_449,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_312])).

cnf(c_450,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_1237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_450])).

cnf(c_1744,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_2054,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_1744])).

cnf(c_3219,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | k1_tops_1(sK0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1750,c_1270,c_1271,c_2054])).

cnf(c_3220,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3219])).

cnf(c_3227,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_3220])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3335,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3227,c_30])).

cnf(c_3336,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3335])).

cnf(c_3739,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3734,c_3336])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_1746,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_3943,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3739,c_1746])).

cnf(c_28,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5380,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3943,c_24,c_28,c_1919,c_1922,c_1925,c_1964,c_2113,c_2175,c_2483,c_3126,c_3485])).

cnf(c_5391,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_5380])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_389,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_390,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1748,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_3141,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_1748])).

cnf(c_3741,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3734,c_3141])).

cnf(c_5394,plain,
    ( r1_tarski(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5391,c_3741])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5412,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5394,c_24,c_29,c_1919,c_1922,c_1925,c_1964,c_2113,c_2175,c_2483,c_3126,c_3485])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1761,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1764,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2833,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1761,c_1764])).

cnf(c_5419,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5412,c_2833])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_405])).

cnf(c_748,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_750,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_748,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5419,c_3734,c_3141,c_750])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.66/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/0.94  
% 2.66/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/0.94  
% 2.66/0.94  ------  iProver source info
% 2.66/0.94  
% 2.66/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.66/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/0.94  git: non_committed_changes: false
% 2.66/0.94  git: last_make_outside_of_git: false
% 2.66/0.94  
% 2.66/0.94  ------ 
% 2.66/0.94  
% 2.66/0.94  ------ Input Options
% 2.66/0.94  
% 2.66/0.94  --out_options                           all
% 2.66/0.94  --tptp_safe_out                         true
% 2.66/0.94  --problem_path                          ""
% 2.66/0.94  --include_path                          ""
% 2.66/0.94  --clausifier                            res/vclausify_rel
% 2.66/0.94  --clausifier_options                    --mode clausify
% 2.66/0.94  --stdin                                 false
% 2.66/0.94  --stats_out                             all
% 2.66/0.94  
% 2.66/0.94  ------ General Options
% 2.66/0.94  
% 2.66/0.94  --fof                                   false
% 2.66/0.94  --time_out_real                         305.
% 2.66/0.94  --time_out_virtual                      -1.
% 2.66/0.94  --symbol_type_check                     false
% 2.66/0.94  --clausify_out                          false
% 2.66/0.94  --sig_cnt_out                           false
% 2.66/0.94  --trig_cnt_out                          false
% 2.66/0.94  --trig_cnt_out_tolerance                1.
% 2.66/0.94  --trig_cnt_out_sk_spl                   false
% 2.66/0.94  --abstr_cl_out                          false
% 2.66/0.94  
% 2.66/0.94  ------ Global Options
% 2.66/0.94  
% 2.66/0.94  --schedule                              default
% 2.66/0.94  --add_important_lit                     false
% 2.66/0.94  --prop_solver_per_cl                    1000
% 2.66/0.94  --min_unsat_core                        false
% 2.66/0.94  --soft_assumptions                      false
% 2.66/0.94  --soft_lemma_size                       3
% 2.66/0.94  --prop_impl_unit_size                   0
% 2.66/0.94  --prop_impl_unit                        []
% 2.66/0.94  --share_sel_clauses                     true
% 2.66/0.94  --reset_solvers                         false
% 2.66/0.94  --bc_imp_inh                            [conj_cone]
% 2.66/0.94  --conj_cone_tolerance                   3.
% 2.66/0.94  --extra_neg_conj                        none
% 2.66/0.94  --large_theory_mode                     true
% 2.66/0.94  --prolific_symb_bound                   200
% 2.66/0.94  --lt_threshold                          2000
% 2.66/0.94  --clause_weak_htbl                      true
% 2.66/0.94  --gc_record_bc_elim                     false
% 2.66/0.94  
% 2.66/0.94  ------ Preprocessing Options
% 2.66/0.94  
% 2.66/0.94  --preprocessing_flag                    true
% 2.66/0.94  --time_out_prep_mult                    0.1
% 2.66/0.94  --splitting_mode                        input
% 2.66/0.94  --splitting_grd                         true
% 2.66/0.94  --splitting_cvd                         false
% 2.66/0.94  --splitting_cvd_svl                     false
% 2.66/0.94  --splitting_nvd                         32
% 2.66/0.94  --sub_typing                            true
% 2.66/0.94  --prep_gs_sim                           true
% 2.66/0.94  --prep_unflatten                        true
% 2.66/0.94  --prep_res_sim                          true
% 2.66/0.94  --prep_upred                            true
% 2.66/0.94  --prep_sem_filter                       exhaustive
% 2.66/0.94  --prep_sem_filter_out                   false
% 2.66/0.94  --pred_elim                             true
% 2.66/0.94  --res_sim_input                         true
% 2.66/0.94  --eq_ax_congr_red                       true
% 2.66/0.94  --pure_diseq_elim                       true
% 2.66/0.94  --brand_transform                       false
% 2.66/0.94  --non_eq_to_eq                          false
% 2.66/0.94  --prep_def_merge                        true
% 2.66/0.94  --prep_def_merge_prop_impl              false
% 2.66/0.94  --prep_def_merge_mbd                    true
% 2.66/0.94  --prep_def_merge_tr_red                 false
% 2.66/0.94  --prep_def_merge_tr_cl                  false
% 2.66/0.94  --smt_preprocessing                     true
% 2.66/0.94  --smt_ac_axioms                         fast
% 2.66/0.94  --preprocessed_out                      false
% 2.66/0.94  --preprocessed_stats                    false
% 2.66/0.94  
% 2.66/0.94  ------ Abstraction refinement Options
% 2.66/0.94  
% 2.66/0.94  --abstr_ref                             []
% 2.66/0.94  --abstr_ref_prep                        false
% 2.66/0.94  --abstr_ref_until_sat                   false
% 2.66/0.94  --abstr_ref_sig_restrict                funpre
% 2.66/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/0.94  --abstr_ref_under                       []
% 2.66/0.94  
% 2.66/0.94  ------ SAT Options
% 2.66/0.94  
% 2.66/0.94  --sat_mode                              false
% 2.66/0.94  --sat_fm_restart_options                ""
% 2.66/0.94  --sat_gr_def                            false
% 2.66/0.94  --sat_epr_types                         true
% 2.66/0.94  --sat_non_cyclic_types                  false
% 2.66/0.94  --sat_finite_models                     false
% 2.66/0.94  --sat_fm_lemmas                         false
% 2.66/0.94  --sat_fm_prep                           false
% 2.66/0.94  --sat_fm_uc_incr                        true
% 2.66/0.94  --sat_out_model                         small
% 2.66/0.94  --sat_out_clauses                       false
% 2.66/0.94  
% 2.66/0.94  ------ QBF Options
% 2.66/0.94  
% 2.66/0.94  --qbf_mode                              false
% 2.66/0.94  --qbf_elim_univ                         false
% 2.66/0.94  --qbf_dom_inst                          none
% 2.66/0.94  --qbf_dom_pre_inst                      false
% 2.66/0.94  --qbf_sk_in                             false
% 2.66/0.94  --qbf_pred_elim                         true
% 2.66/0.94  --qbf_split                             512
% 2.66/0.94  
% 2.66/0.94  ------ BMC1 Options
% 2.66/0.94  
% 2.66/0.94  --bmc1_incremental                      false
% 2.66/0.94  --bmc1_axioms                           reachable_all
% 2.66/0.94  --bmc1_min_bound                        0
% 2.66/0.94  --bmc1_max_bound                        -1
% 2.66/0.94  --bmc1_max_bound_default                -1
% 2.66/0.94  --bmc1_symbol_reachability              true
% 2.66/0.94  --bmc1_property_lemmas                  false
% 2.66/0.94  --bmc1_k_induction                      false
% 2.66/0.94  --bmc1_non_equiv_states                 false
% 2.66/0.94  --bmc1_deadlock                         false
% 2.66/0.94  --bmc1_ucm                              false
% 2.66/0.94  --bmc1_add_unsat_core                   none
% 2.66/0.94  --bmc1_unsat_core_children              false
% 2.66/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/0.94  --bmc1_out_stat                         full
% 2.66/0.94  --bmc1_ground_init                      false
% 2.66/0.94  --bmc1_pre_inst_next_state              false
% 2.66/0.94  --bmc1_pre_inst_state                   false
% 2.66/0.94  --bmc1_pre_inst_reach_state             false
% 2.66/0.94  --bmc1_out_unsat_core                   false
% 2.66/0.94  --bmc1_aig_witness_out                  false
% 2.66/0.94  --bmc1_verbose                          false
% 2.66/0.94  --bmc1_dump_clauses_tptp                false
% 2.66/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.66/0.94  --bmc1_dump_file                        -
% 2.66/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.66/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.66/0.94  --bmc1_ucm_extend_mode                  1
% 2.66/0.94  --bmc1_ucm_init_mode                    2
% 2.66/0.94  --bmc1_ucm_cone_mode                    none
% 2.66/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.66/0.94  --bmc1_ucm_relax_model                  4
% 2.66/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.66/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/0.94  --bmc1_ucm_layered_model                none
% 2.66/0.94  --bmc1_ucm_max_lemma_size               10
% 2.66/0.94  
% 2.66/0.94  ------ AIG Options
% 2.66/0.94  
% 2.66/0.94  --aig_mode                              false
% 2.66/0.94  
% 2.66/0.94  ------ Instantiation Options
% 2.66/0.94  
% 2.66/0.94  --instantiation_flag                    true
% 2.66/0.94  --inst_sos_flag                         false
% 2.66/0.94  --inst_sos_phase                        true
% 2.66/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/0.94  --inst_lit_sel_side                     num_symb
% 2.66/0.94  --inst_solver_per_active                1400
% 2.66/0.94  --inst_solver_calls_frac                1.
% 2.66/0.94  --inst_passive_queue_type               priority_queues
% 2.66/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/0.94  --inst_passive_queues_freq              [25;2]
% 2.66/0.94  --inst_dismatching                      true
% 2.66/0.94  --inst_eager_unprocessed_to_passive     true
% 2.66/0.94  --inst_prop_sim_given                   true
% 2.66/0.94  --inst_prop_sim_new                     false
% 2.66/0.94  --inst_subs_new                         false
% 2.66/0.94  --inst_eq_res_simp                      false
% 2.66/0.94  --inst_subs_given                       false
% 2.66/0.94  --inst_orphan_elimination               true
% 2.66/0.94  --inst_learning_loop_flag               true
% 2.66/0.94  --inst_learning_start                   3000
% 2.66/0.94  --inst_learning_factor                  2
% 2.66/0.94  --inst_start_prop_sim_after_learn       3
% 2.66/0.94  --inst_sel_renew                        solver
% 2.66/0.94  --inst_lit_activity_flag                true
% 2.66/0.94  --inst_restr_to_given                   false
% 2.66/0.94  --inst_activity_threshold               500
% 2.66/0.94  --inst_out_proof                        true
% 2.66/0.94  
% 2.66/0.94  ------ Resolution Options
% 2.66/0.94  
% 2.66/0.94  --resolution_flag                       true
% 2.66/0.94  --res_lit_sel                           adaptive
% 2.66/0.94  --res_lit_sel_side                      none
% 2.66/0.94  --res_ordering                          kbo
% 2.66/0.94  --res_to_prop_solver                    active
% 2.66/0.94  --res_prop_simpl_new                    false
% 2.66/0.94  --res_prop_simpl_given                  true
% 2.66/0.94  --res_passive_queue_type                priority_queues
% 2.66/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/0.94  --res_passive_queues_freq               [15;5]
% 2.66/0.94  --res_forward_subs                      full
% 2.66/0.94  --res_backward_subs                     full
% 2.66/0.94  --res_forward_subs_resolution           true
% 2.66/0.94  --res_backward_subs_resolution          true
% 2.66/0.94  --res_orphan_elimination                true
% 2.66/0.94  --res_time_limit                        2.
% 2.66/0.94  --res_out_proof                         true
% 2.66/0.94  
% 2.66/0.94  ------ Superposition Options
% 2.66/0.94  
% 2.66/0.94  --superposition_flag                    true
% 2.66/0.94  --sup_passive_queue_type                priority_queues
% 2.66/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.66/0.94  --demod_completeness_check              fast
% 2.66/0.94  --demod_use_ground                      true
% 2.66/0.94  --sup_to_prop_solver                    passive
% 2.66/0.94  --sup_prop_simpl_new                    true
% 2.66/0.94  --sup_prop_simpl_given                  true
% 2.66/0.94  --sup_fun_splitting                     false
% 2.66/0.94  --sup_smt_interval                      50000
% 2.66/0.94  
% 2.66/0.94  ------ Superposition Simplification Setup
% 2.66/0.94  
% 2.66/0.94  --sup_indices_passive                   []
% 2.66/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.94  --sup_full_bw                           [BwDemod]
% 2.66/0.94  --sup_immed_triv                        [TrivRules]
% 2.66/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.94  --sup_immed_bw_main                     []
% 2.66/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.94  
% 2.66/0.94  ------ Combination Options
% 2.66/0.94  
% 2.66/0.94  --comb_res_mult                         3
% 2.66/0.94  --comb_sup_mult                         2
% 2.66/0.94  --comb_inst_mult                        10
% 2.66/0.94  
% 2.66/0.94  ------ Debug Options
% 2.66/0.94  
% 2.66/0.94  --dbg_backtrace                         false
% 2.66/0.94  --dbg_dump_prop_clauses                 false
% 2.66/0.94  --dbg_dump_prop_clauses_file            -
% 2.66/0.94  --dbg_out_stat                          false
% 2.66/0.94  ------ Parsing...
% 2.66/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/0.94  
% 2.66/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.66/0.94  
% 2.66/0.94  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/0.94  
% 2.66/0.94  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/0.94  ------ Proving...
% 2.66/0.94  ------ Problem Properties 
% 2.66/0.94  
% 2.66/0.94  
% 2.66/0.94  clauses                                 23
% 2.66/0.94  conjectures                             6
% 2.66/0.94  EPR                                     9
% 2.66/0.94  Horn                                    20
% 2.66/0.94  unary                                   3
% 2.66/0.94  binary                                  12
% 2.66/0.94  lits                                    56
% 2.66/0.94  lits eq                                 7
% 2.66/0.94  fd_pure                                 0
% 2.66/0.94  fd_pseudo                               0
% 2.66/0.94  fd_cond                                 1
% 2.66/0.94  fd_pseudo_cond                          1
% 2.66/0.94  AC symbols                              0
% 2.66/0.94  
% 2.66/0.94  ------ Schedule dynamic 5 is on 
% 2.66/0.94  
% 2.66/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/0.94  
% 2.66/0.94  
% 2.66/0.94  ------ 
% 2.66/0.94  Current options:
% 2.66/0.94  ------ 
% 2.66/0.94  
% 2.66/0.94  ------ Input Options
% 2.66/0.94  
% 2.66/0.94  --out_options                           all
% 2.66/0.94  --tptp_safe_out                         true
% 2.66/0.94  --problem_path                          ""
% 2.66/0.94  --include_path                          ""
% 2.66/0.94  --clausifier                            res/vclausify_rel
% 2.66/0.94  --clausifier_options                    --mode clausify
% 2.66/0.94  --stdin                                 false
% 2.66/0.94  --stats_out                             all
% 2.66/0.94  
% 2.66/0.94  ------ General Options
% 2.66/0.94  
% 2.66/0.94  --fof                                   false
% 2.66/0.94  --time_out_real                         305.
% 2.66/0.94  --time_out_virtual                      -1.
% 2.66/0.94  --symbol_type_check                     false
% 2.66/0.94  --clausify_out                          false
% 2.66/0.94  --sig_cnt_out                           false
% 2.66/0.94  --trig_cnt_out                          false
% 2.66/0.94  --trig_cnt_out_tolerance                1.
% 2.66/0.94  --trig_cnt_out_sk_spl                   false
% 2.66/0.94  --abstr_cl_out                          false
% 2.66/0.94  
% 2.66/0.94  ------ Global Options
% 2.66/0.94  
% 2.66/0.94  --schedule                              default
% 2.66/0.94  --add_important_lit                     false
% 2.66/0.94  --prop_solver_per_cl                    1000
% 2.66/0.94  --min_unsat_core                        false
% 2.66/0.94  --soft_assumptions                      false
% 2.66/0.94  --soft_lemma_size                       3
% 2.66/0.94  --prop_impl_unit_size                   0
% 2.66/0.94  --prop_impl_unit                        []
% 2.66/0.94  --share_sel_clauses                     true
% 2.66/0.94  --reset_solvers                         false
% 2.66/0.94  --bc_imp_inh                            [conj_cone]
% 2.66/0.94  --conj_cone_tolerance                   3.
% 2.66/0.94  --extra_neg_conj                        none
% 2.66/0.94  --large_theory_mode                     true
% 2.66/0.94  --prolific_symb_bound                   200
% 2.66/0.94  --lt_threshold                          2000
% 2.66/0.94  --clause_weak_htbl                      true
% 2.66/0.94  --gc_record_bc_elim                     false
% 2.66/0.94  
% 2.66/0.94  ------ Preprocessing Options
% 2.66/0.94  
% 2.66/0.94  --preprocessing_flag                    true
% 2.66/0.94  --time_out_prep_mult                    0.1
% 2.66/0.94  --splitting_mode                        input
% 2.66/0.94  --splitting_grd                         true
% 2.66/0.94  --splitting_cvd                         false
% 2.66/0.94  --splitting_cvd_svl                     false
% 2.66/0.94  --splitting_nvd                         32
% 2.66/0.94  --sub_typing                            true
% 2.66/0.94  --prep_gs_sim                           true
% 2.66/0.94  --prep_unflatten                        true
% 2.66/0.94  --prep_res_sim                          true
% 2.66/0.94  --prep_upred                            true
% 2.66/0.94  --prep_sem_filter                       exhaustive
% 2.66/0.94  --prep_sem_filter_out                   false
% 2.66/0.94  --pred_elim                             true
% 2.66/0.94  --res_sim_input                         true
% 2.66/0.94  --eq_ax_congr_red                       true
% 2.66/0.94  --pure_diseq_elim                       true
% 2.66/0.94  --brand_transform                       false
% 2.66/0.94  --non_eq_to_eq                          false
% 2.66/0.94  --prep_def_merge                        true
% 2.66/0.94  --prep_def_merge_prop_impl              false
% 2.66/0.94  --prep_def_merge_mbd                    true
% 2.66/0.94  --prep_def_merge_tr_red                 false
% 2.66/0.94  --prep_def_merge_tr_cl                  false
% 2.66/0.94  --smt_preprocessing                     true
% 2.66/0.94  --smt_ac_axioms                         fast
% 2.66/0.94  --preprocessed_out                      false
% 2.66/0.94  --preprocessed_stats                    false
% 2.66/0.94  
% 2.66/0.94  ------ Abstraction refinement Options
% 2.66/0.94  
% 2.66/0.94  --abstr_ref                             []
% 2.66/0.94  --abstr_ref_prep                        false
% 2.66/0.94  --abstr_ref_until_sat                   false
% 2.66/0.94  --abstr_ref_sig_restrict                funpre
% 2.66/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/0.94  --abstr_ref_under                       []
% 2.66/0.94  
% 2.66/0.94  ------ SAT Options
% 2.66/0.94  
% 2.66/0.94  --sat_mode                              false
% 2.66/0.94  --sat_fm_restart_options                ""
% 2.66/0.94  --sat_gr_def                            false
% 2.66/0.94  --sat_epr_types                         true
% 2.66/0.94  --sat_non_cyclic_types                  false
% 2.66/0.94  --sat_finite_models                     false
% 2.66/0.94  --sat_fm_lemmas                         false
% 2.66/0.94  --sat_fm_prep                           false
% 2.66/0.94  --sat_fm_uc_incr                        true
% 2.66/0.94  --sat_out_model                         small
% 2.66/0.94  --sat_out_clauses                       false
% 2.66/0.94  
% 2.66/0.94  ------ QBF Options
% 2.66/0.94  
% 2.66/0.94  --qbf_mode                              false
% 2.66/0.94  --qbf_elim_univ                         false
% 2.66/0.94  --qbf_dom_inst                          none
% 2.66/0.94  --qbf_dom_pre_inst                      false
% 2.66/0.94  --qbf_sk_in                             false
% 2.66/0.94  --qbf_pred_elim                         true
% 2.66/0.94  --qbf_split                             512
% 2.66/0.94  
% 2.66/0.94  ------ BMC1 Options
% 2.66/0.94  
% 2.66/0.94  --bmc1_incremental                      false
% 2.66/0.94  --bmc1_axioms                           reachable_all
% 2.66/0.94  --bmc1_min_bound                        0
% 2.66/0.94  --bmc1_max_bound                        -1
% 2.66/0.94  --bmc1_max_bound_default                -1
% 2.66/0.94  --bmc1_symbol_reachability              true
% 2.66/0.94  --bmc1_property_lemmas                  false
% 2.66/0.94  --bmc1_k_induction                      false
% 2.66/0.94  --bmc1_non_equiv_states                 false
% 2.66/0.94  --bmc1_deadlock                         false
% 2.66/0.94  --bmc1_ucm                              false
% 2.66/0.94  --bmc1_add_unsat_core                   none
% 2.66/0.94  --bmc1_unsat_core_children              false
% 2.66/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/0.94  --bmc1_out_stat                         full
% 2.66/0.94  --bmc1_ground_init                      false
% 2.66/0.94  --bmc1_pre_inst_next_state              false
% 2.66/0.94  --bmc1_pre_inst_state                   false
% 2.66/0.94  --bmc1_pre_inst_reach_state             false
% 2.66/0.94  --bmc1_out_unsat_core                   false
% 2.66/0.94  --bmc1_aig_witness_out                  false
% 2.66/0.94  --bmc1_verbose                          false
% 2.66/0.94  --bmc1_dump_clauses_tptp                false
% 2.66/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.66/0.94  --bmc1_dump_file                        -
% 2.66/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.66/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.66/0.94  --bmc1_ucm_extend_mode                  1
% 2.66/0.94  --bmc1_ucm_init_mode                    2
% 2.66/0.94  --bmc1_ucm_cone_mode                    none
% 2.66/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.66/0.94  --bmc1_ucm_relax_model                  4
% 2.66/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.66/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/0.94  --bmc1_ucm_layered_model                none
% 2.66/0.94  --bmc1_ucm_max_lemma_size               10
% 2.66/0.94  
% 2.66/0.94  ------ AIG Options
% 2.66/0.94  
% 2.66/0.94  --aig_mode                              false
% 2.66/0.94  
% 2.66/0.94  ------ Instantiation Options
% 2.66/0.94  
% 2.66/0.94  --instantiation_flag                    true
% 2.66/0.94  --inst_sos_flag                         false
% 2.66/0.94  --inst_sos_phase                        true
% 2.66/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/0.94  --inst_lit_sel_side                     none
% 2.66/0.94  --inst_solver_per_active                1400
% 2.66/0.94  --inst_solver_calls_frac                1.
% 2.66/0.94  --inst_passive_queue_type               priority_queues
% 2.66/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/0.94  --inst_passive_queues_freq              [25;2]
% 2.66/0.94  --inst_dismatching                      true
% 2.66/0.94  --inst_eager_unprocessed_to_passive     true
% 2.66/0.94  --inst_prop_sim_given                   true
% 2.66/0.94  --inst_prop_sim_new                     false
% 2.66/0.94  --inst_subs_new                         false
% 2.66/0.94  --inst_eq_res_simp                      false
% 2.66/0.94  --inst_subs_given                       false
% 2.66/0.94  --inst_orphan_elimination               true
% 2.66/0.94  --inst_learning_loop_flag               true
% 2.66/0.94  --inst_learning_start                   3000
% 2.66/0.94  --inst_learning_factor                  2
% 2.66/0.94  --inst_start_prop_sim_after_learn       3
% 2.66/0.94  --inst_sel_renew                        solver
% 2.66/0.94  --inst_lit_activity_flag                true
% 2.66/0.94  --inst_restr_to_given                   false
% 2.66/0.94  --inst_activity_threshold               500
% 2.66/0.94  --inst_out_proof                        true
% 2.66/0.94  
% 2.66/0.94  ------ Resolution Options
% 2.66/0.94  
% 2.66/0.94  --resolution_flag                       false
% 2.66/0.94  --res_lit_sel                           adaptive
% 2.66/0.94  --res_lit_sel_side                      none
% 2.66/0.94  --res_ordering                          kbo
% 2.66/0.94  --res_to_prop_solver                    active
% 2.66/0.94  --res_prop_simpl_new                    false
% 2.66/0.94  --res_prop_simpl_given                  true
% 2.66/0.94  --res_passive_queue_type                priority_queues
% 2.66/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/0.94  --res_passive_queues_freq               [15;5]
% 2.66/0.94  --res_forward_subs                      full
% 2.66/0.94  --res_backward_subs                     full
% 2.66/0.94  --res_forward_subs_resolution           true
% 2.66/0.94  --res_backward_subs_resolution          true
% 2.66/0.94  --res_orphan_elimination                true
% 2.66/0.94  --res_time_limit                        2.
% 2.66/0.94  --res_out_proof                         true
% 2.66/0.94  
% 2.66/0.94  ------ Superposition Options
% 2.66/0.94  
% 2.66/0.94  --superposition_flag                    true
% 2.66/0.94  --sup_passive_queue_type                priority_queues
% 2.66/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.66/0.94  --demod_completeness_check              fast
% 2.66/0.94  --demod_use_ground                      true
% 2.66/0.94  --sup_to_prop_solver                    passive
% 2.66/0.94  --sup_prop_simpl_new                    true
% 2.66/0.94  --sup_prop_simpl_given                  true
% 2.66/0.94  --sup_fun_splitting                     false
% 2.66/0.94  --sup_smt_interval                      50000
% 2.66/0.94  
% 2.66/0.94  ------ Superposition Simplification Setup
% 2.66/0.94  
% 2.66/0.94  --sup_indices_passive                   []
% 2.66/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.94  --sup_full_bw                           [BwDemod]
% 2.66/0.94  --sup_immed_triv                        [TrivRules]
% 2.66/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.94  --sup_immed_bw_main                     []
% 2.66/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.94  
% 2.66/0.94  ------ Combination Options
% 2.66/0.94  
% 2.66/0.94  --comb_res_mult                         3
% 2.66/0.94  --comb_sup_mult                         2
% 2.66/0.94  --comb_inst_mult                        10
% 2.66/0.94  
% 2.66/0.94  ------ Debug Options
% 2.66/0.94  
% 2.66/0.94  --dbg_backtrace                         false
% 2.66/0.94  --dbg_dump_prop_clauses                 false
% 2.66/0.94  --dbg_dump_prop_clauses_file            -
% 2.66/0.94  --dbg_out_stat                          false
% 2.66/0.94  
% 2.66/0.94  
% 2.66/0.94  
% 2.66/0.94  
% 2.66/0.94  ------ Proving...
% 2.66/0.94  
% 2.66/0.94  
% 2.66/0.94  % SZS status Theorem for theBenchmark.p
% 2.66/0.94  
% 2.66/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/0.94  
% 2.66/0.94  fof(f10,conjecture,(
% 2.66/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f11,negated_conjecture,(
% 2.66/0.94    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.66/0.94    inference(negated_conjecture,[],[f10])).
% 2.66/0.94  
% 2.66/0.94  fof(f22,plain,(
% 2.66/0.94    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.66/0.94    inference(ennf_transformation,[],[f11])).
% 2.66/0.94  
% 2.66/0.94  fof(f23,plain,(
% 2.66/0.94    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.66/0.94    inference(flattening,[],[f22])).
% 2.66/0.94  
% 2.66/0.94  fof(f28,plain,(
% 2.66/0.94    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.66/0.94    inference(nnf_transformation,[],[f23])).
% 2.66/0.94  
% 2.66/0.94  fof(f29,plain,(
% 2.66/0.94    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.66/0.94    inference(flattening,[],[f28])).
% 2.66/0.94  
% 2.66/0.94  fof(f30,plain,(
% 2.66/0.94    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.66/0.94    inference(rectify,[],[f29])).
% 2.66/0.94  
% 2.66/0.94  fof(f33,plain,(
% 2.66/0.94    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.66/0.94    introduced(choice_axiom,[])).
% 2.66/0.94  
% 2.66/0.94  fof(f32,plain,(
% 2.66/0.94    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.66/0.94    introduced(choice_axiom,[])).
% 2.66/0.94  
% 2.66/0.94  fof(f31,plain,(
% 2.66/0.94    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.66/0.94    introduced(choice_axiom,[])).
% 2.66/0.94  
% 2.66/0.94  fof(f34,plain,(
% 2.66/0.94    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.66/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).
% 2.66/0.94  
% 2.66/0.94  fof(f51,plain,(
% 2.66/0.94    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.66/0.94    inference(cnf_transformation,[],[f34])).
% 2.66/0.94  
% 2.66/0.94  fof(f4,axiom,(
% 2.66/0.94    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f26,plain,(
% 2.66/0.94    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.66/0.94    inference(nnf_transformation,[],[f4])).
% 2.66/0.94  
% 2.66/0.94  fof(f41,plain,(
% 2.66/0.94    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f26])).
% 2.66/0.94  
% 2.66/0.94  fof(f52,plain,(
% 2.66/0.94    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f34])).
% 2.66/0.94  
% 2.66/0.94  fof(f5,axiom,(
% 2.66/0.94    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f14,plain,(
% 2.66/0.94    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.66/0.94    inference(ennf_transformation,[],[f5])).
% 2.66/0.94  
% 2.66/0.94  fof(f15,plain,(
% 2.66/0.94    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.94    inference(flattening,[],[f14])).
% 2.66/0.94  
% 2.66/0.94  fof(f42,plain,(
% 2.66/0.94    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f15])).
% 2.66/0.94  
% 2.66/0.94  fof(f49,plain,(
% 2.66/0.94    v2_pre_topc(sK0)),
% 2.66/0.94    inference(cnf_transformation,[],[f34])).
% 2.66/0.94  
% 2.66/0.94  fof(f50,plain,(
% 2.66/0.94    l1_pre_topc(sK0)),
% 2.66/0.94    inference(cnf_transformation,[],[f34])).
% 2.66/0.94  
% 2.66/0.94  fof(f9,axiom,(
% 2.66/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f21,plain,(
% 2.66/0.94    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.94    inference(ennf_transformation,[],[f9])).
% 2.66/0.94  
% 2.66/0.94  fof(f27,plain,(
% 2.66/0.94    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.94    inference(nnf_transformation,[],[f21])).
% 2.66/0.94  
% 2.66/0.94  fof(f48,plain,(
% 2.66/0.94    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f27])).
% 2.66/0.94  
% 2.66/0.94  fof(f6,axiom,(
% 2.66/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f16,plain,(
% 2.66/0.94    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.94    inference(ennf_transformation,[],[f6])).
% 2.66/0.94  
% 2.66/0.94  fof(f43,plain,(
% 2.66/0.94    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f16])).
% 2.66/0.94  
% 2.66/0.94  fof(f40,plain,(
% 2.66/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.66/0.94    inference(cnf_transformation,[],[f26])).
% 2.66/0.94  
% 2.66/0.94  fof(f2,axiom,(
% 2.66/0.94    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f12,plain,(
% 2.66/0.94    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.66/0.94    inference(ennf_transformation,[],[f2])).
% 2.66/0.94  
% 2.66/0.94  fof(f13,plain,(
% 2.66/0.94    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.66/0.94    inference(flattening,[],[f12])).
% 2.66/0.94  
% 2.66/0.94  fof(f38,plain,(
% 2.66/0.94    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f13])).
% 2.66/0.94  
% 2.66/0.94  fof(f53,plain,(
% 2.66/0.94    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.66/0.94    inference(cnf_transformation,[],[f34])).
% 2.66/0.94  
% 2.66/0.94  fof(f8,axiom,(
% 2.66/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f19,plain,(
% 2.66/0.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.66/0.94    inference(ennf_transformation,[],[f8])).
% 2.66/0.94  
% 2.66/0.94  fof(f20,plain,(
% 2.66/0.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.94    inference(flattening,[],[f19])).
% 2.66/0.94  
% 2.66/0.94  fof(f45,plain,(
% 2.66/0.94    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f20])).
% 2.66/0.94  
% 2.66/0.94  fof(f46,plain,(
% 2.66/0.94    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f20])).
% 2.66/0.94  
% 2.66/0.94  fof(f55,plain,(
% 2.66/0.94    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.66/0.94    inference(cnf_transformation,[],[f34])).
% 2.66/0.94  
% 2.66/0.94  fof(f7,axiom,(
% 2.66/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f17,plain,(
% 2.66/0.94    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.94    inference(ennf_transformation,[],[f7])).
% 2.66/0.94  
% 2.66/0.94  fof(f18,plain,(
% 2.66/0.94    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.94    inference(flattening,[],[f17])).
% 2.66/0.94  
% 2.66/0.94  fof(f44,plain,(
% 2.66/0.94    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f18])).
% 2.66/0.94  
% 2.66/0.94  fof(f47,plain,(
% 2.66/0.94    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f27])).
% 2.66/0.94  
% 2.66/0.94  fof(f54,plain,(
% 2.66/0.94    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.66/0.94    inference(cnf_transformation,[],[f34])).
% 2.66/0.94  
% 2.66/0.94  fof(f3,axiom,(
% 2.66/0.94    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f39,plain,(
% 2.66/0.94    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f3])).
% 2.66/0.94  
% 2.66/0.94  fof(f1,axiom,(
% 2.66/0.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.66/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.94  
% 2.66/0.94  fof(f24,plain,(
% 2.66/0.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.66/0.94    inference(nnf_transformation,[],[f1])).
% 2.66/0.94  
% 2.66/0.94  fof(f25,plain,(
% 2.66/0.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.66/0.94    inference(flattening,[],[f24])).
% 2.66/0.94  
% 2.66/0.94  fof(f37,plain,(
% 2.66/0.94    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.66/0.94    inference(cnf_transformation,[],[f25])).
% 2.66/0.94  
% 2.66/0.94  fof(f56,plain,(
% 2.66/0.94    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.66/0.94    inference(cnf_transformation,[],[f34])).
% 2.66/0.94  
% 2.66/0.94  cnf(c_19,negated_conjecture,
% 2.66/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.66/0.94      inference(cnf_transformation,[],[f51]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1753,plain,
% 2.66/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_5,plain,
% 2.66/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.66/0.94      inference(cnf_transformation,[],[f41]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1760,plain,
% 2.66/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.66/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_18,negated_conjecture,
% 2.66/0.94      ( v2_tops_1(sK1,sK0)
% 2.66/0.94      | ~ v3_pre_topc(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ r1_tarski(X0,sK1)
% 2.66/0.94      | k1_xboole_0 = X0 ),
% 2.66/0.94      inference(cnf_transformation,[],[f52]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1754,plain,
% 2.66/0.94      ( k1_xboole_0 = X0
% 2.66/0.94      | v2_tops_1(sK1,sK0) = iProver_top
% 2.66/0.94      | v3_pre_topc(X0,sK0) != iProver_top
% 2.66/0.94      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | r1_tarski(X0,sK1) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2356,plain,
% 2.66/0.94      ( k1_xboole_0 = X0
% 2.66/0.94      | v2_tops_1(sK1,sK0) = iProver_top
% 2.66/0.94      | v3_pre_topc(X0,sK0) != iProver_top
% 2.66/0.94      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.66/0.94      | r1_tarski(X0,sK1) != iProver_top ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_1760,c_1754]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_24,plain,
% 2.66/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_7,plain,
% 2.66/0.94      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.66/0.94      | ~ v2_pre_topc(X0)
% 2.66/0.94      | ~ l1_pre_topc(X0) ),
% 2.66/0.94      inference(cnf_transformation,[],[f42]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_21,negated_conjecture,
% 2.66/0.94      ( v2_pre_topc(sK0) ),
% 2.66/0.94      inference(cnf_transformation,[],[f49]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_288,plain,
% 2.66/0.94      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.66/0.94      | ~ l1_pre_topc(X0)
% 2.66/0.94      | sK0 != X0 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_289,plain,
% 2.66/0.94      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ l1_pre_topc(sK0) ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_288]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_20,negated_conjecture,
% 2.66/0.94      ( l1_pre_topc(sK0) ),
% 2.66/0.94      inference(cnf_transformation,[],[f50]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_293,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_289,c_20]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_294,plain,
% 2.66/0.94      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.66/0.94      inference(renaming,[status(thm)],[c_293]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1918,plain,
% 2.66/0.94      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 2.66/0.94      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_294]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1919,plain,
% 2.66/0.94      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top
% 2.66/0.94      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_1918]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_12,plain,
% 2.66/0.94      ( v2_tops_1(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ l1_pre_topc(X1)
% 2.66/0.94      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.66/0.94      inference(cnf_transformation,[],[f48]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_404,plain,
% 2.66/0.94      ( v2_tops_1(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.66/0.94      | sK0 != X1 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_405,plain,
% 2.66/0.94      ( v2_tops_1(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_404]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1921,plain,
% 2.66/0.94      ( v2_tops_1(sK1,sK0)
% 2.66/0.94      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_405]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1922,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.66/0.94      | v2_tops_1(sK1,sK0) = iProver_top
% 2.66/0.94      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_1921]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_8,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.66/0.94      | ~ l1_pre_topc(X1) ),
% 2.66/0.94      inference(cnf_transformation,[],[f43]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_437,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.66/0.94      | sK0 != X1 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_438,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_437]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1924,plain,
% 2.66/0.94      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_438]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1925,plain,
% 2.66/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1963,plain,
% 2.66/0.94      ( v2_tops_1(sK1,sK0)
% 2.66/0.94      | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 2.66/0.94      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.66/0.94      | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_18]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1964,plain,
% 2.66/0.94      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 2.66/0.94      | v2_tops_1(sK1,sK0) = iProver_top
% 2.66/0.94      | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 2.66/0.94      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_1963]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1243,plain,( X0 = X0 ),theory(equality) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2113,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_1243]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_6,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.66/0.94      inference(cnf_transformation,[],[f40]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2004,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_6]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2174,plain,
% 2.66/0.94      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_2004]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2175,plain,
% 2.66/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_2174]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3,plain,
% 2.66/0.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.66/0.94      inference(cnf_transformation,[],[f38]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2015,plain,
% 2.66/0.94      ( ~ r1_tarski(X0,X1)
% 2.66/0.94      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 2.66/0.94      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_3]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2300,plain,
% 2.66/0.94      ( r1_tarski(X0,u1_struct_0(sK0))
% 2.66/0.94      | ~ r1_tarski(X0,sK1)
% 2.66/0.94      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_2015]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2482,plain,
% 2.66/0.94      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 2.66/0.94      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.66/0.94      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_2300]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2483,plain,
% 2.66/0.94      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 2.66/0.94      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 2.66/0.94      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_2482]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1940,plain,
% 2.66/0.94      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_5]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3125,plain,
% 2.66/0.94      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_1940]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3126,plain,
% 2.66/0.94      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.66/0.94      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_3125]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1244,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1991,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK1) != X0
% 2.66/0.94      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.66/0.94      | k1_xboole_0 != X0 ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_1244]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3485,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 2.66/0.94      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.66/0.94      | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 2.66/0.94      inference(instantiation,[status(thm)],[c_1991]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3734,plain,
% 2.66/0.94      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_2356,c_24,c_1919,c_1922,c_1925,c_1964,c_2113,c_2175,
% 2.66/0.94                 c_2483,c_3126,c_3485]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_17,negated_conjecture,
% 2.66/0.94      ( ~ v2_tops_1(sK1,sK0)
% 2.66/0.94      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.66/0.94      inference(cnf_transformation,[],[f53]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1755,plain,
% 2.66/0.94      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.66/0.94      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_11,plain,
% 2.66/0.94      ( ~ v3_pre_topc(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ v2_pre_topc(X3)
% 2.66/0.94      | ~ l1_pre_topc(X3)
% 2.66/0.94      | ~ l1_pre_topc(X1)
% 2.66/0.94      | k1_tops_1(X1,X0) = X0 ),
% 2.66/0.94      inference(cnf_transformation,[],[f45]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_331,plain,
% 2.66/0.94      ( ~ v3_pre_topc(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.66/0.94      | ~ l1_pre_topc(X1)
% 2.66/0.94      | ~ l1_pre_topc(X3)
% 2.66/0.94      | k1_tops_1(X1,X0) = X0
% 2.66/0.94      | sK0 != X3 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_332,plain,
% 2.66/0.94      ( ~ v3_pre_topc(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ l1_pre_topc(X1)
% 2.66/0.94      | ~ l1_pre_topc(sK0)
% 2.66/0.94      | k1_tops_1(X1,X0) = X0 ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_331]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_336,plain,
% 2.66/0.94      ( ~ l1_pre_topc(X1)
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ v3_pre_topc(X0,X1)
% 2.66/0.94      | k1_tops_1(X1,X0) = X0 ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_332,c_20]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_337,plain,
% 2.66/0.94      ( ~ v3_pre_topc(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ l1_pre_topc(X1)
% 2.66/0.94      | k1_tops_1(X1,X0) = X0 ),
% 2.66/0.94      inference(renaming,[status(thm)],[c_336]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_371,plain,
% 2.66/0.94      ( ~ v3_pre_topc(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(X1,X0) = X0
% 2.66/0.94      | sK0 != X1 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_337,c_20]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_372,plain,
% 2.66/0.94      ( ~ v3_pre_topc(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,X0) = X0 ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_371]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1240,plain,
% 2.66/0.94      ( ~ v3_pre_topc(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,X0) = X0
% 2.66/0.94      | ~ sP2_iProver_split ),
% 2.66/0.94      inference(splitting,
% 2.66/0.94                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.66/0.94                [c_372]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1750,plain,
% 2.66/0.94      ( k1_tops_1(sK0,X0) = X0
% 2.66/0.94      | v3_pre_topc(X0,sK0) != iProver_top
% 2.66/0.94      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | sP2_iProver_split != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1241,plain,
% 2.66/0.94      ( sP2_iProver_split | sP0_iProver_split ),
% 2.66/0.94      inference(splitting,
% 2.66/0.94                [splitting(split),new_symbols(definition,[])],
% 2.66/0.94                [c_372]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1270,plain,
% 2.66/0.94      ( sP2_iProver_split = iProver_top
% 2.66/0.94      | sP0_iProver_split = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1271,plain,
% 2.66/0.94      ( k1_tops_1(sK0,X0) = X0
% 2.66/0.94      | v3_pre_topc(X0,sK0) != iProver_top
% 2.66/0.94      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | sP2_iProver_split != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_10,plain,
% 2.66/0.94      ( v3_pre_topc(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.66/0.94      | ~ v2_pre_topc(X1)
% 2.66/0.94      | ~ l1_pre_topc(X1)
% 2.66/0.94      | ~ l1_pre_topc(X3)
% 2.66/0.94      | k1_tops_1(X1,X0) != X0 ),
% 2.66/0.94      inference(cnf_transformation,[],[f46]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_306,plain,
% 2.66/0.94      ( v3_pre_topc(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.66/0.94      | ~ l1_pre_topc(X1)
% 2.66/0.94      | ~ l1_pre_topc(X3)
% 2.66/0.94      | k1_tops_1(X1,X0) != X0
% 2.66/0.94      | sK0 != X1 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_307,plain,
% 2.66/0.94      ( v3_pre_topc(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ l1_pre_topc(X2)
% 2.66/0.94      | ~ l1_pre_topc(sK0)
% 2.66/0.94      | k1_tops_1(sK0,X0) != X0 ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_306]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_311,plain,
% 2.66/0.94      ( ~ l1_pre_topc(X2)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.66/0.94      | v3_pre_topc(X0,sK0)
% 2.66/0.94      | k1_tops_1(sK0,X0) != X0 ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_307,c_20]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_312,plain,
% 2.66/0.94      ( v3_pre_topc(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ l1_pre_topc(X2)
% 2.66/0.94      | k1_tops_1(sK0,X0) != X0 ),
% 2.66/0.94      inference(renaming,[status(thm)],[c_311]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_449,plain,
% 2.66/0.94      ( v3_pre_topc(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,X0) != X0
% 2.66/0.94      | sK0 != X2 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_20,c_312]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_450,plain,
% 2.66/0.94      ( v3_pre_topc(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,X0) != X0 ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_449]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1237,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ sP0_iProver_split ),
% 2.66/0.94      inference(splitting,
% 2.66/0.94                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.66/0.94                [c_450]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1744,plain,
% 2.66/0.94      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | sP0_iProver_split != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_1237]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2054,plain,
% 2.66/0.94      ( sP0_iProver_split != iProver_top ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_1753,c_1744]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3219,plain,
% 2.66/0.94      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | v3_pre_topc(X0,sK0) != iProver_top
% 2.66/0.94      | k1_tops_1(sK0,X0) = X0 ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_1750,c_1270,c_1271,c_2054]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3220,plain,
% 2.66/0.94      ( k1_tops_1(sK0,X0) = X0
% 2.66/0.94      | v3_pre_topc(X0,sK0) != iProver_top
% 2.66/0.94      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.66/0.94      inference(renaming,[status(thm)],[c_3219]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3227,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK2) = sK2
% 2.66/0.94      | v2_tops_1(sK1,sK0) != iProver_top
% 2.66/0.94      | v3_pre_topc(sK2,sK0) != iProver_top ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_1755,c_3220]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_15,negated_conjecture,
% 2.66/0.94      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.66/0.94      inference(cnf_transformation,[],[f55]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_30,plain,
% 2.66/0.94      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.66/0.94      | v3_pre_topc(sK2,sK0) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3335,plain,
% 2.66/0.94      ( v2_tops_1(sK1,sK0) != iProver_top | k1_tops_1(sK0,sK2) = sK2 ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_3227,c_30]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3336,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK2) = sK2 | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.66/0.94      inference(renaming,[status(thm)],[c_3335]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3739,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK2) = sK2 ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_3734,c_3336]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_9,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ r1_tarski(X0,X2)
% 2.66/0.94      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.66/0.94      | ~ l1_pre_topc(X1) ),
% 2.66/0.94      inference(cnf_transformation,[],[f44]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_419,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ r1_tarski(X0,X2)
% 2.66/0.94      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.66/0.94      | sK0 != X1 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_420,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | ~ r1_tarski(X0,X1)
% 2.66/0.94      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_419]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1746,plain,
% 2.66/0.94      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | r1_tarski(X0,X1) != iProver_top
% 2.66/0.94      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3943,plain,
% 2.66/0.94      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | r1_tarski(sK2,X0) != iProver_top
% 2.66/0.94      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_3739,c_1746]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_28,plain,
% 2.66/0.94      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.66/0.94      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_5380,plain,
% 2.66/0.94      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.66/0.94      | r1_tarski(sK2,X0) != iProver_top
% 2.66/0.94      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_3943,c_24,c_28,c_1919,c_1922,c_1925,c_1964,c_2113,
% 2.66/0.94                 c_2175,c_2483,c_3126,c_3485]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_5391,plain,
% 2.66/0.94      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.66/0.94      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_1753,c_5380]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_13,plain,
% 2.66/0.94      ( ~ v2_tops_1(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | ~ l1_pre_topc(X1)
% 2.66/0.94      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.66/0.94      inference(cnf_transformation,[],[f47]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_389,plain,
% 2.66/0.94      ( ~ v2_tops_1(X0,X1)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.66/0.94      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.66/0.94      | sK0 != X1 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_390,plain,
% 2.66/0.94      ( ~ v2_tops_1(X0,sK0)
% 2.66/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_389]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1748,plain,
% 2.66/0.94      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.66/0.94      | v2_tops_1(X0,sK0) != iProver_top
% 2.66/0.94      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3141,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.66/0.94      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_1753,c_1748]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_3741,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_3734,c_3141]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_5394,plain,
% 2.66/0.94      ( r1_tarski(sK2,sK1) != iProver_top
% 2.66/0.94      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.66/0.94      inference(light_normalisation,[status(thm)],[c_5391,c_3741]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_16,negated_conjecture,
% 2.66/0.94      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.66/0.94      inference(cnf_transformation,[],[f54]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_29,plain,
% 2.66/0.94      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.66/0.94      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_5412,plain,
% 2.66/0.94      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_5394,c_24,c_29,c_1919,c_1922,c_1925,c_1964,c_2113,
% 2.66/0.94                 c_2175,c_2483,c_3126,c_3485]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_4,plain,
% 2.66/0.94      ( r1_tarski(k1_xboole_0,X0) ),
% 2.66/0.94      inference(cnf_transformation,[],[f39]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1761,plain,
% 2.66/0.94      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_0,plain,
% 2.66/0.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.66/0.94      inference(cnf_transformation,[],[f37]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_1764,plain,
% 2.66/0.94      ( X0 = X1
% 2.66/0.94      | r1_tarski(X0,X1) != iProver_top
% 2.66/0.94      | r1_tarski(X1,X0) != iProver_top ),
% 2.66/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_2833,plain,
% 2.66/0.94      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_1761,c_1764]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_5419,plain,
% 2.66/0.94      ( sK2 = k1_xboole_0 ),
% 2.66/0.94      inference(superposition,[status(thm)],[c_5412,c_2833]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_14,negated_conjecture,
% 2.66/0.94      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.66/0.94      inference(cnf_transformation,[],[f56]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_747,plain,
% 2.66/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.66/0.94      | sK0 != sK0
% 2.66/0.94      | sK1 != X0
% 2.66/0.94      | sK2 != k1_xboole_0 ),
% 2.66/0.94      inference(resolution_lifted,[status(thm)],[c_14,c_405]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_748,plain,
% 2.66/0.94      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.66/0.94      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.66/0.94      | sK2 != k1_xboole_0 ),
% 2.66/0.94      inference(unflattening,[status(thm)],[c_747]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(c_750,plain,
% 2.66/0.94      ( k1_tops_1(sK0,sK1) != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.66/0.94      inference(global_propositional_subsumption,
% 2.66/0.94                [status(thm)],
% 2.66/0.94                [c_748,c_19]) ).
% 2.66/0.94  
% 2.66/0.94  cnf(contradiction,plain,
% 2.66/0.94      ( $false ),
% 2.66/0.94      inference(minisat,[status(thm)],[c_5419,c_3734,c_3141,c_750]) ).
% 2.66/0.94  
% 2.66/0.94  
% 2.66/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/0.94  
% 2.66/0.94  ------                               Statistics
% 2.66/0.94  
% 2.66/0.94  ------ General
% 2.66/0.94  
% 2.66/0.94  abstr_ref_over_cycles:                  0
% 2.66/0.94  abstr_ref_under_cycles:                 0
% 2.66/0.94  gc_basic_clause_elim:                   0
% 2.66/0.94  forced_gc_time:                         0
% 2.66/0.94  parsing_time:                           0.008
% 2.66/0.94  unif_index_cands_time:                  0.
% 2.66/0.94  unif_index_add_time:                    0.
% 2.66/0.94  orderings_time:                         0.
% 2.66/0.94  out_proof_time:                         0.016
% 2.66/0.94  total_time:                             0.185
% 2.66/0.94  num_of_symbols:                         47
% 2.66/0.94  num_of_terms:                           2411
% 2.66/0.94  
% 2.66/0.94  ------ Preprocessing
% 2.66/0.94  
% 2.66/0.94  num_of_splits:                          4
% 2.66/0.94  num_of_split_atoms:                     3
% 2.66/0.94  num_of_reused_defs:                     1
% 2.66/0.94  num_eq_ax_congr_red:                    4
% 2.66/0.94  num_of_sem_filtered_clauses:            4
% 2.66/0.94  num_of_subtypes:                        0
% 2.66/0.94  monotx_restored_types:                  0
% 2.66/0.94  sat_num_of_epr_types:                   0
% 2.66/0.94  sat_num_of_non_cyclic_types:            0
% 2.66/0.94  sat_guarded_non_collapsed_types:        0
% 2.66/0.94  num_pure_diseq_elim:                    0
% 2.66/0.94  simp_replaced_by:                       0
% 2.66/0.94  res_preprocessed:                       100
% 2.66/0.94  prep_upred:                             0
% 2.66/0.94  prep_unflattend:                        27
% 2.66/0.94  smt_new_axioms:                         0
% 2.66/0.94  pred_elim_cands:                        4
% 2.66/0.94  pred_elim:                              2
% 2.66/0.94  pred_elim_cl:                           2
% 2.66/0.94  pred_elim_cycles:                       6
% 2.66/0.94  merged_defs:                            8
% 2.66/0.94  merged_defs_ncl:                        0
% 2.66/0.94  bin_hyper_res:                          8
% 2.66/0.94  prep_cycles:                            4
% 2.66/0.94  pred_elim_time:                         0.014
% 2.66/0.94  splitting_time:                         0.
% 2.66/0.94  sem_filter_time:                        0.
% 2.66/0.94  monotx_time:                            0.
% 2.66/0.94  subtype_inf_time:                       0.
% 2.66/0.94  
% 2.66/0.94  ------ Problem properties
% 2.66/0.94  
% 2.66/0.94  clauses:                                23
% 2.66/0.94  conjectures:                            6
% 2.66/0.94  epr:                                    9
% 2.66/0.94  horn:                                   20
% 2.66/0.94  ground:                                 7
% 2.66/0.94  unary:                                  3
% 2.66/0.94  binary:                                 12
% 2.66/0.94  lits:                                   56
% 2.66/0.94  lits_eq:                                7
% 2.66/0.94  fd_pure:                                0
% 2.66/0.94  fd_pseudo:                              0
% 2.66/0.94  fd_cond:                                1
% 2.66/0.94  fd_pseudo_cond:                         1
% 2.66/0.94  ac_symbols:                             0
% 2.66/0.94  
% 2.66/0.94  ------ Propositional Solver
% 2.66/0.94  
% 2.66/0.94  prop_solver_calls:                      29
% 2.66/0.94  prop_fast_solver_calls:                 914
% 2.66/0.94  smt_solver_calls:                       0
% 2.66/0.94  smt_fast_solver_calls:                  0
% 2.66/0.94  prop_num_of_clauses:                    1665
% 2.66/0.94  prop_preprocess_simplified:             5011
% 2.66/0.94  prop_fo_subsumed:                       41
% 2.66/0.94  prop_solver_time:                       0.
% 2.66/0.94  smt_solver_time:                        0.
% 2.66/0.94  smt_fast_solver_time:                   0.
% 2.66/0.94  prop_fast_solver_time:                  0.
% 2.66/0.94  prop_unsat_core_time:                   0.
% 2.66/0.94  
% 2.66/0.94  ------ QBF
% 2.66/0.94  
% 2.66/0.94  qbf_q_res:                              0
% 2.66/0.94  qbf_num_tautologies:                    0
% 2.66/0.94  qbf_prep_cycles:                        0
% 2.66/0.94  
% 2.66/0.94  ------ BMC1
% 2.66/0.94  
% 2.66/0.94  bmc1_current_bound:                     -1
% 2.66/0.94  bmc1_last_solved_bound:                 -1
% 2.66/0.94  bmc1_unsat_core_size:                   -1
% 2.66/0.94  bmc1_unsat_core_parents_size:           -1
% 2.66/0.94  bmc1_merge_next_fun:                    0
% 2.66/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.66/0.94  
% 2.66/0.94  ------ Instantiation
% 2.66/0.94  
% 2.66/0.94  inst_num_of_clauses:                    528
% 2.66/0.94  inst_num_in_passive:                    195
% 2.66/0.94  inst_num_in_active:                     300
% 2.66/0.94  inst_num_in_unprocessed:                34
% 2.66/0.94  inst_num_of_loops:                      330
% 2.66/0.94  inst_num_of_learning_restarts:          0
% 2.66/0.94  inst_num_moves_active_passive:          25
% 2.66/0.94  inst_lit_activity:                      0
% 2.66/0.94  inst_lit_activity_moves:                0
% 2.66/0.94  inst_num_tautologies:                   0
% 2.66/0.94  inst_num_prop_implied:                  0
% 2.66/0.94  inst_num_existing_simplified:           0
% 2.66/0.94  inst_num_eq_res_simplified:             0
% 2.66/0.94  inst_num_child_elim:                    0
% 2.66/0.94  inst_num_of_dismatching_blockings:      122
% 2.66/0.94  inst_num_of_non_proper_insts:           798
% 2.66/0.94  inst_num_of_duplicates:                 0
% 2.66/0.94  inst_inst_num_from_inst_to_res:         0
% 2.66/0.94  inst_dismatching_checking_time:         0.
% 2.66/0.94  
% 2.66/0.94  ------ Resolution
% 2.66/0.94  
% 2.66/0.94  res_num_of_clauses:                     0
% 2.66/0.94  res_num_in_passive:                     0
% 2.66/0.94  res_num_in_active:                      0
% 2.66/0.94  res_num_of_loops:                       104
% 2.66/0.94  res_forward_subset_subsumed:            77
% 2.66/0.94  res_backward_subset_subsumed:           4
% 2.66/0.94  res_forward_subsumed:                   0
% 2.66/0.94  res_backward_subsumed:                  0
% 2.66/0.94  res_forward_subsumption_resolution:     0
% 2.66/0.94  res_backward_subsumption_resolution:    0
% 2.66/0.94  res_clause_to_clause_subsumption:       496
% 2.66/0.94  res_orphan_elimination:                 0
% 2.66/0.94  res_tautology_del:                      109
% 2.66/0.94  res_num_eq_res_simplified:              0
% 2.66/0.94  res_num_sel_changes:                    0
% 2.66/0.94  res_moves_from_active_to_pass:          0
% 2.66/0.94  
% 2.66/0.94  ------ Superposition
% 2.66/0.94  
% 2.66/0.94  sup_time_total:                         0.
% 2.66/0.94  sup_time_generating:                    0.
% 2.66/0.94  sup_time_sim_full:                      0.
% 2.66/0.94  sup_time_sim_immed:                     0.
% 2.66/0.94  
% 2.66/0.94  sup_num_of_clauses:                     78
% 2.66/0.94  sup_num_in_active:                      55
% 2.66/0.94  sup_num_in_passive:                     23
% 2.66/0.94  sup_num_of_loops:                       65
% 2.66/0.94  sup_fw_superposition:                   67
% 2.66/0.94  sup_bw_superposition:                   38
% 2.66/0.94  sup_immediate_simplified:               28
% 2.66/0.94  sup_given_eliminated:                   2
% 2.66/0.94  comparisons_done:                       0
% 2.66/0.94  comparisons_avoided:                    0
% 2.66/0.94  
% 2.66/0.94  ------ Simplifications
% 2.66/0.94  
% 2.66/0.94  
% 2.66/0.94  sim_fw_subset_subsumed:                 9
% 2.66/0.94  sim_bw_subset_subsumed:                 7
% 2.66/0.94  sim_fw_subsumed:                        10
% 2.66/0.94  sim_bw_subsumed:                        1
% 2.66/0.94  sim_fw_subsumption_res:                 0
% 2.66/0.94  sim_bw_subsumption_res:                 0
% 2.66/0.94  sim_tautology_del:                      7
% 2.66/0.94  sim_eq_tautology_del:                   3
% 2.66/0.94  sim_eq_res_simp:                        0
% 2.66/0.94  sim_fw_demodulated:                     0
% 2.66/0.94  sim_bw_demodulated:                     10
% 2.66/0.94  sim_light_normalised:                   9
% 2.66/0.94  sim_joinable_taut:                      0
% 2.66/0.94  sim_joinable_simp:                      0
% 2.66/0.94  sim_ac_normalised:                      0
% 2.66/0.94  sim_smt_subsumption:                    0
% 2.66/0.94  
%------------------------------------------------------------------------------

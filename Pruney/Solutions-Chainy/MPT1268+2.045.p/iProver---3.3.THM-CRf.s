%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:11 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  152 (1171 expanded)
%              Number of clauses        :   89 ( 294 expanded)
%              Number of leaves         :   17 ( 293 expanded)
%              Depth                    :   26
%              Number of atoms          :  550 (9436 expanded)
%              Number of equality atoms :  189 (1680 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f61,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_879,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_894,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2433,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_894])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_885,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1341,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_885])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1141,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1169,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1174,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_18,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1252,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1357,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1341])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1242,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1395,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_268,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1401,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1427,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_269,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1263,plain,
    ( k1_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_1666,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1689,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1341,c_21,c_20,c_19,c_1141,c_1169,c_1174,c_1252,c_1357,c_1395,c_1401,c_1427,c_1666])).

cnf(c_2436,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2433,c_1689])).

cnf(c_23,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2783,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2436,c_23])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_899,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2790,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2783,c_899])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_902,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3316,plain,
    ( r1_xboole_0(k1_xboole_0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2790,c_902])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_881,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_893,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3134,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1689,c_893])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5474,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3134,c_23,c_24])).

cnf(c_5475,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5474])).

cnf(c_5484,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_5475])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_262,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_11])).

cnf(c_888,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_22,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_263,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_11])).

cnf(c_300,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_301,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_11])).

cnf(c_1761,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_1762,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1761])).

cnf(c_2912,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | k1_tops_1(X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_888,c_22,c_23,c_24,c_300,c_301,c_1762])).

cnf(c_2913,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2912])).

cnf(c_2923,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_2913])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_12,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1182,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2009,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ sP1_iProver_split
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_3468,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2923,c_21,c_20,c_19,c_17,c_15,c_263,c_1141,c_1169,c_1174,c_1182,c_1252,c_1357,c_1395,c_1401,c_1427,c_1666,c_1761,c_2009])).

cnf(c_5492,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5484,c_3468])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1183,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1182])).

cnf(c_5738,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5492,c_21,c_20,c_23,c_19,c_24,c_29,c_1141,c_1169,c_1174,c_1183,c_1252,c_1357,c_1395,c_1401,c_1427,c_1666])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_898,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5744,plain,
    ( r1_xboole_0(sK2,X0) = iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5738,c_898])).

cnf(c_6523,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3316,c_5744])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_901,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9817,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6523,c_901])).

cnf(c_880,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1275,plain,
    ( sK1 = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_880])).

cnf(c_1801,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1275,c_21,c_20,c_23,c_19,c_24,c_1141,c_1169,c_1174,c_1183,c_1252,c_1357,c_1395,c_1401,c_1427,c_1666])).

cnf(c_882,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1807,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_882])).

cnf(c_1922,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_1807,c_899])).

cnf(c_11224,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9817,c_1922])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_884,plain,
    ( k1_xboole_0 != sK2
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11575,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11224,c_884])).

cnf(c_11576,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11575])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11576,c_1689,c_1183,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:37:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.85/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.99  
% 3.85/0.99  ------  iProver source info
% 3.85/0.99  
% 3.85/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.99  git: non_committed_changes: false
% 3.85/0.99  git: last_make_outside_of_git: false
% 3.85/0.99  
% 3.85/0.99  ------ 
% 3.85/0.99  ------ Parsing...
% 3.85/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.99  ------ Proving...
% 3.85/0.99  ------ Problem Properties 
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  clauses                                 26
% 3.85/0.99  conjectures                             8
% 3.85/0.99  EPR                                     9
% 3.85/0.99  Horn                                    23
% 3.85/0.99  unary                                   3
% 3.85/0.99  binary                                  11
% 3.85/0.99  lits                                    74
% 3.85/0.99  lits eq                                 9
% 3.85/0.99  fd_pure                                 0
% 3.85/0.99  fd_pseudo                               0
% 3.85/0.99  fd_cond                                 1
% 3.85/0.99  fd_pseudo_cond                          0
% 3.85/0.99  AC symbols                              0
% 3.85/0.99  
% 3.85/0.99  ------ Input Options Time Limit: Unbounded
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  ------ 
% 3.85/0.99  Current options:
% 3.85/0.99  ------ 
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  ------ Proving...
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS status Theorem for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  fof(f12,conjecture,(
% 3.85/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f13,negated_conjecture,(
% 3.85/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 3.85/0.99    inference(negated_conjecture,[],[f12])).
% 3.85/0.99  
% 3.85/0.99  fof(f27,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f13])).
% 3.85/0.99  
% 3.85/0.99  fof(f28,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.85/0.99    inference(flattening,[],[f27])).
% 3.85/0.99  
% 3.85/0.99  fof(f32,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.85/0.99    inference(nnf_transformation,[],[f28])).
% 3.85/0.99  
% 3.85/0.99  fof(f33,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.85/0.99    inference(flattening,[],[f32])).
% 3.85/0.99  
% 3.85/0.99  fof(f34,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.85/0.99    inference(rectify,[],[f33])).
% 3.85/0.99  
% 3.85/0.99  fof(f37,plain,(
% 3.85/0.99    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f36,plain,(
% 3.85/0.99    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f35,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f38,plain,(
% 3.85/0.99    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).
% 3.85/0.99  
% 3.85/0.99  fof(f56,plain,(
% 3.85/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.85/0.99    inference(cnf_transformation,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f8,axiom,(
% 3.85/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f21,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/0.99    inference(ennf_transformation,[],[f8])).
% 3.85/0.99  
% 3.85/0.99  fof(f48,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f21])).
% 3.85/0.99  
% 3.85/0.99  fof(f11,axiom,(
% 3.85/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f26,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/0.99    inference(ennf_transformation,[],[f11])).
% 3.85/0.99  
% 3.85/0.99  fof(f31,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/0.99    inference(nnf_transformation,[],[f26])).
% 3.85/0.99  
% 3.85/0.99  fof(f52,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f31])).
% 3.85/0.99  
% 3.85/0.99  fof(f54,plain,(
% 3.85/0.99    v2_pre_topc(sK0)),
% 3.85/0.99    inference(cnf_transformation,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f55,plain,(
% 3.85/0.99    l1_pre_topc(sK0)),
% 3.85/0.99    inference(cnf_transformation,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f6,axiom,(
% 3.85/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f30,plain,(
% 3.85/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.85/0.99    inference(nnf_transformation,[],[f6])).
% 3.85/0.99  
% 3.85/0.99  fof(f45,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f30])).
% 3.85/0.99  
% 3.85/0.99  fof(f7,axiom,(
% 3.85/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f19,plain,(
% 3.85/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f7])).
% 3.85/0.99  
% 3.85/0.99  fof(f20,plain,(
% 3.85/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.85/0.99    inference(flattening,[],[f19])).
% 3.85/0.99  
% 3.85/0.99  fof(f47,plain,(
% 3.85/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f20])).
% 3.85/0.99  
% 3.85/0.99  fof(f57,plain,(
% 3.85/0.99    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f2,axiom,(
% 3.85/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f14,plain,(
% 3.85/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(ennf_transformation,[],[f2])).
% 3.85/0.99  
% 3.85/0.99  fof(f15,plain,(
% 3.85/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.85/0.99    inference(flattening,[],[f14])).
% 3.85/0.99  
% 3.85/0.99  fof(f41,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f15])).
% 3.85/0.99  
% 3.85/0.99  fof(f46,plain,(
% 3.85/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f30])).
% 3.85/0.99  
% 3.85/0.99  fof(f3,axiom,(
% 3.85/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f16,plain,(
% 3.85/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.85/0.99    inference(ennf_transformation,[],[f3])).
% 3.85/0.99  
% 3.85/0.99  fof(f42,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f16])).
% 3.85/0.99  
% 3.85/0.99  fof(f5,axiom,(
% 3.85/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f44,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f5])).
% 3.85/0.99  
% 3.85/0.99  fof(f64,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f42,f44])).
% 3.85/0.99  
% 3.85/0.99  fof(f1,axiom,(
% 3.85/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f29,plain,(
% 3.85/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.85/0.99    inference(nnf_transformation,[],[f1])).
% 3.85/0.99  
% 3.85/0.99  fof(f40,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.85/0.99    inference(cnf_transformation,[],[f29])).
% 3.85/0.99  
% 3.85/0.99  fof(f62,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.85/0.99    inference(definition_unfolding,[],[f40,f44])).
% 3.85/0.99  
% 3.85/0.99  fof(f58,plain,(
% 3.85/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 3.85/0.99    inference(cnf_transformation,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f9,axiom,(
% 3.85/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f22,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/0.99    inference(ennf_transformation,[],[f9])).
% 3.85/0.99  
% 3.85/0.99  fof(f23,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/0.99    inference(flattening,[],[f22])).
% 3.85/0.99  
% 3.85/0.99  fof(f49,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f23])).
% 3.85/0.99  
% 3.85/0.99  fof(f10,axiom,(
% 3.85/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f24,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f10])).
% 3.85/0.99  
% 3.85/0.99  fof(f25,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.85/0.99    inference(flattening,[],[f24])).
% 3.85/0.99  
% 3.85/0.99  fof(f50,plain,(
% 3.85/0.99    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f25])).
% 3.85/0.99  
% 3.85/0.99  fof(f60,plain,(
% 3.85/0.99    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 3.85/0.99    inference(cnf_transformation,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f53,plain,(
% 3.85/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f31])).
% 3.85/0.99  
% 3.85/0.99  fof(f59,plain,(
% 3.85/0.99    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 3.85/0.99    inference(cnf_transformation,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f4,axiom,(
% 3.85/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f17,plain,(
% 3.85/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(ennf_transformation,[],[f4])).
% 3.85/0.99  
% 3.85/0.99  fof(f18,plain,(
% 3.85/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.85/0.99    inference(flattening,[],[f17])).
% 3.85/0.99  
% 3.85/0.99  fof(f43,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f18])).
% 3.85/0.99  
% 3.85/0.99  fof(f39,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f29])).
% 3.85/0.99  
% 3.85/0.99  fof(f63,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f39,f44])).
% 3.85/0.99  
% 3.85/0.99  fof(f61,plain,(
% 3.85/0.99    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 3.85/0.99    inference(cnf_transformation,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  cnf(c_19,negated_conjecture,
% 3.85/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_879,plain,
% 3.85/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_8,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.85/0.99      | ~ l1_pre_topc(X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_894,plain,
% 3.85/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.85/0.99      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 3.85/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2433,plain,
% 3.85/0.99      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 3.85/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_879,c_894]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_13,plain,
% 3.85/0.99      ( ~ v2_tops_1(X0,X1)
% 3.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ l1_pre_topc(X1)
% 3.85/0.99      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_885,plain,
% 3.85/0.99      ( k1_tops_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | v2_tops_1(X1,X0) != iProver_top
% 3.85/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.85/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1341,plain,
% 3.85/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.85/0.99      | v2_tops_1(sK1,sK0) != iProver_top
% 3.85/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_879,c_885]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_21,negated_conjecture,
% 3.85/0.99      ( v2_pre_topc(sK0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_20,negated_conjecture,
% 3.85/0.99      ( l1_pre_topc(sK0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1141,plain,
% 3.85/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1169,plain,
% 3.85/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 3.85/0.99      | ~ l1_pre_topc(sK0) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7,plain,
% 3.85/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.85/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.85/0.99      | ~ v2_pre_topc(X0)
% 3.85/0.99      | ~ l1_pre_topc(X0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1174,plain,
% 3.85/0.99      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 3.85/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | ~ v2_pre_topc(sK0)
% 3.85/0.99      | ~ l1_pre_topc(sK0) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_18,negated_conjecture,
% 3.85/0.99      ( v2_tops_1(sK1,sK0)
% 3.85/0.99      | ~ v3_pre_topc(X0,sK0)
% 3.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | ~ r1_tarski(X0,sK1)
% 3.85/0.99      | k1_xboole_0 = X0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1252,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0)
% 3.85/0.99      | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 3.85/0.99      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 3.85/0.99      | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1357,plain,
% 3.85/0.99      ( ~ v2_tops_1(sK1,sK0)
% 3.85/0.99      | ~ l1_pre_topc(sK0)
% 3.85/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.85/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1341]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2,plain,
% 3.85/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1242,plain,
% 3.85/0.99      ( r1_tarski(k1_tops_1(sK0,sK1),X0)
% 3.85/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 3.85/0.99      | ~ r1_tarski(sK1,X0) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1395,plain,
% 3.85/0.99      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 3.85/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 3.85/0.99      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_1242]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_268,plain,( X0 = X0 ),theory(equality) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1401,plain,
% 3.85/0.99      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_268]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5,plain,
% 3.85/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1427,plain,
% 3.85/0.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_269,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1263,plain,
% 3.85/0.99      ( k1_tops_1(sK0,sK1) != X0
% 3.85/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.85/0.99      | k1_xboole_0 != X0 ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_269]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1666,plain,
% 3.85/0.99      ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 3.85/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.85/0.99      | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_1263]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1689,plain,
% 3.85/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_1341,c_21,c_20,c_19,c_1141,c_1169,c_1174,c_1252,
% 3.85/0.99                 c_1357,c_1395,c_1401,c_1427,c_1666]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2436,plain,
% 3.85/0.99      ( r1_tarski(k1_xboole_0,sK1) = iProver_top
% 3.85/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.85/0.99      inference(light_normalisation,[status(thm)],[c_2433,c_1689]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_23,plain,
% 3.85/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2783,plain,
% 3.85/0.99      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_2436,c_23]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3,plain,
% 3.85/0.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_899,plain,
% 3.85/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 3.85/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2790,plain,
% 3.85/0.99      ( k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) = k1_xboole_0 ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2783,c_899]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_0,plain,
% 3.85/0.99      ( r1_xboole_0(X0,X1)
% 3.85/0.99      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_902,plain,
% 3.85/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 3.85/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3316,plain,
% 3.85/0.99      ( r1_xboole_0(k1_xboole_0,sK1) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2790,c_902]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_17,negated_conjecture,
% 3.85/0.99      ( ~ v2_tops_1(sK1,sK0)
% 3.85/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_881,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.85/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_9,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ r1_tarski(X0,X2)
% 3.85/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.85/0.99      | ~ l1_pre_topc(X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_893,plain,
% 3.85/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.85/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.85/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.85/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
% 3.85/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3134,plain,
% 3.85/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.85/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.85/0.99      | r1_tarski(X0,sK1) != iProver_top
% 3.85/0.99      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top
% 3.85/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1689,c_893]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_24,plain,
% 3.85/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5474,plain,
% 3.85/0.99      ( r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top
% 3.85/0.99      | r1_tarski(X0,sK1) != iProver_top
% 3.85/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_3134,c_23,c_24]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5475,plain,
% 3.85/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.85/0.99      | r1_tarski(X0,sK1) != iProver_top
% 3.85/0.99      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_5474]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5484,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.85/0.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_xboole_0) = iProver_top
% 3.85/0.99      | r1_tarski(sK2,sK1) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_881,c_5475]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_11,plain,
% 3.85/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.85/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ v2_pre_topc(X3)
% 3.85/0.99      | ~ l1_pre_topc(X3)
% 3.85/0.99      | ~ l1_pre_topc(X1)
% 3.85/0.99      | k1_tops_1(X1,X0) = X0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_262,plain,
% 3.85/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ l1_pre_topc(X1)
% 3.85/0.99      | k1_tops_1(X1,X0) = X0
% 3.85/0.99      | ~ sP1_iProver_split ),
% 3.85/0.99      inference(splitting,
% 3.85/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.85/0.99                [c_11]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_888,plain,
% 3.85/0.99      ( k1_tops_1(X0,X1) = X1
% 3.85/0.99      | v3_pre_topc(X1,X0) != iProver_top
% 3.85/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.85/0.99      | l1_pre_topc(X0) != iProver_top
% 3.85/0.99      | sP1_iProver_split != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_22,plain,
% 3.85/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_263,plain,
% 3.85/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 3.85/0.99      inference(splitting,
% 3.85/0.99                [splitting(split),new_symbols(definition,[])],
% 3.85/0.99                [c_11]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_300,plain,
% 3.85/0.99      ( sP1_iProver_split = iProver_top
% 3.85/0.99      | sP0_iProver_split = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_301,plain,
% 3.85/0.99      ( k1_tops_1(X0,X1) = X1
% 3.85/0.99      | v3_pre_topc(X1,X0) != iProver_top
% 3.85/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.85/0.99      | l1_pre_topc(X0) != iProver_top
% 3.85/0.99      | sP1_iProver_split != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_261,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ v2_pre_topc(X1)
% 3.85/0.99      | ~ l1_pre_topc(X1)
% 3.85/0.99      | ~ sP0_iProver_split ),
% 3.85/0.99      inference(splitting,
% 3.85/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.85/0.99                [c_11]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1761,plain,
% 3.85/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | ~ v2_pre_topc(sK0)
% 3.85/0.99      | ~ l1_pre_topc(sK0)
% 3.85/0.99      | ~ sP0_iProver_split ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_261]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1762,plain,
% 3.85/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.85/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.85/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.85/0.99      | sP0_iProver_split != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1761]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2912,plain,
% 3.85/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.85/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.85/0.99      | v3_pre_topc(X1,X0) != iProver_top
% 3.85/0.99      | k1_tops_1(X0,X1) = X1 ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_888,c_22,c_23,c_24,c_300,c_301,c_1762]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2913,plain,
% 3.85/0.99      ( k1_tops_1(X0,X1) = X1
% 3.85/0.99      | v3_pre_topc(X1,X0) != iProver_top
% 3.85/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.85/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_2912]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2923,plain,
% 3.85/0.99      ( k1_tops_1(sK0,sK2) = sK2
% 3.85/0.99      | v2_tops_1(sK1,sK0) != iProver_top
% 3.85/0.99      | v3_pre_topc(sK2,sK0) != iProver_top
% 3.85/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_881,c_2913]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_15,negated_conjecture,
% 3.85/0.99      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_12,plain,
% 3.85/0.99      ( v2_tops_1(X0,X1)
% 3.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ l1_pre_topc(X1)
% 3.85/0.99      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1182,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0)
% 3.85/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | ~ l1_pre_topc(sK0)
% 3.85/0.99      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2009,plain,
% 3.85/0.99      ( ~ v3_pre_topc(sK2,sK0)
% 3.85/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.85/0.99      | ~ l1_pre_topc(sK0)
% 3.85/0.99      | ~ sP1_iProver_split
% 3.85/0.99      | k1_tops_1(sK0,sK2) = sK2 ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_262]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3468,plain,
% 3.85/0.99      ( k1_tops_1(sK0,sK2) = sK2 ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_2923,c_21,c_20,c_19,c_17,c_15,c_263,c_1141,c_1169,
% 3.85/0.99                 c_1174,c_1182,c_1252,c_1357,c_1395,c_1401,c_1427,c_1666,
% 3.85/0.99                 c_1761,c_2009]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5492,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.85/0.99      | r1_tarski(sK2,sK1) != iProver_top
% 3.85/0.99      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.85/0.99      inference(light_normalisation,[status(thm)],[c_5484,c_3468]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_16,negated_conjecture,
% 3.85/0.99      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_29,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.85/0.99      | r1_tarski(sK2,sK1) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1183,plain,
% 3.85/0.99      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.85/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 3.85/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.85/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1182]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5738,plain,
% 3.85/0.99      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_5492,c_21,c_20,c_23,c_19,c_24,c_29,c_1141,c_1169,
% 3.85/0.99                 c_1174,c_1183,c_1252,c_1357,c_1395,c_1401,c_1427,c_1666]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4,plain,
% 3.85/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 3.85/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_898,plain,
% 3.85/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.85/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.85/0.99      | r1_xboole_0(X0,X2) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5744,plain,
% 3.85/0.99      ( r1_xboole_0(sK2,X0) = iProver_top
% 3.85/0.99      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_5738,c_898]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6523,plain,
% 3.85/0.99      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_3316,c_5744]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1,plain,
% 3.85/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.85/0.99      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_901,plain,
% 3.85/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 3.85/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_9817,plain,
% 3.85/0.99      ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_xboole_0 ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_6523,c_901]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_880,plain,
% 3.85/0.99      ( k1_xboole_0 = X0
% 3.85/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 3.85/0.99      | v3_pre_topc(X0,sK0) != iProver_top
% 3.85/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.85/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1275,plain,
% 3.85/0.99      ( sK1 = k1_xboole_0
% 3.85/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 3.85/0.99      | v3_pre_topc(sK1,sK0) != iProver_top
% 3.85/0.99      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_879,c_880]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1801,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_1275,c_21,c_20,c_23,c_19,c_24,c_1141,c_1169,c_1174,
% 3.85/0.99                 c_1183,c_1252,c_1357,c_1395,c_1401,c_1427,c_1666]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_882,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.85/0.99      | r1_tarski(sK2,sK1) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1807,plain,
% 3.85/0.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1801,c_882]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1922,plain,
% 3.85/0.99      ( k1_setfam_1(k2_tarski(sK2,sK1)) = sK2 ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1807,c_899]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_11224,plain,
% 3.85/0.99      ( sK2 = k1_xboole_0 ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_9817,c_1922]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_14,negated_conjecture,
% 3.85/0.99      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 3.85/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_884,plain,
% 3.85/0.99      ( k1_xboole_0 != sK2 | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_11575,plain,
% 3.85/0.99      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_11224,c_884]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_11576,plain,
% 3.85/0.99      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 3.85/0.99      inference(equality_resolution_simp,[status(thm)],[c_11575]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(contradiction,plain,
% 3.85/0.99      ( $false ),
% 3.85/0.99      inference(minisat,[status(thm)],[c_11576,c_1689,c_1183,c_24,c_23]) ).
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  ------                               Statistics
% 3.85/0.99  
% 3.85/0.99  ------ Selected
% 3.85/0.99  
% 3.85/0.99  total_time:                             0.481
% 3.85/0.99  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:23 EST 2020

% Result     : Theorem 55.09s
% Output     : CNFRefutation 55.09s
% Verified   : 
% Statistics : Number of formulae       :  192 (1488 expanded)
%              Number of clauses        :  114 ( 356 expanded)
%              Number of leaves         :   20 ( 352 expanded)
%              Depth                    :   24
%              Number of atoms          :  688 (6799 expanded)
%              Number of equality atoms :  279 (2024 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK3),sK3) != k2_tops_1(X0,sK3)
          | ~ v3_pre_topc(sK3,X0) )
        & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK3),sK3) = k2_tops_1(X0,sK3)
          | v3_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X1),X1) != k2_tops_1(sK2,X1)
            | ~ v3_pre_topc(X1,sK2) )
          & ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X1),X1) = k2_tops_1(sK2,X1)
            | v3_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
      | ~ v3_pre_topc(sK3,sK2) )
    & ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f70,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f49,f72])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f61])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_24,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_205,plain,
    ( v3_pre_topc(sK3,sK2)
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_380,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_381,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_385,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_26])).

cnf(c_386,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_385])).

cnf(c_417,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(X1,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_386,c_26])).

cnf(c_418,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,X0) = X0
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_205,c_418])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_25])).

cnf(c_717,plain,
    ( sP0_iProver_split
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_515])).

cnf(c_1145,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) = sK3
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_23,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_203,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_355,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_356,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_360,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_26])).

cnf(c_361,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_471,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_361])).

cnf(c_472,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,X0) != X0
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_472])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_25])).

cnf(c_715,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_536])).

cnf(c_1373,plain,
    ( ~ sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_715,c_25])).

cnf(c_1560,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1145,c_717,c_1373])).

cnf(c_1561,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_1560])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1164,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1165,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1150,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_1147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1151,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2627,plain,
    ( k5_xboole_0(k2_pre_topc(sK2,X0),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,X0),X1))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1151])).

cnf(c_3447,plain,
    ( k5_xboole_0(k2_pre_topc(sK2,sK3),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,sK3),X0))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_1150,c_2627])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1156,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4071,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_1156])).

cnf(c_5932,plain,
    ( k1_setfam_1(k2_tarski(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1))) = X2
    | r2_hidden(sK0(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1),X2),X1) != iProver_top
    | r2_hidden(sK0(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1),X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_4071])).

cnf(c_108802,plain,
    ( k1_setfam_1(k2_tarski(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0))) = X1
    | r2_hidden(sK0(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_5932])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4069,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1156])).

cnf(c_5377,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_4069])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_85,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5391,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_4069])).

cnf(c_5937,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_4069])).

cnf(c_48239,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5377,c_85,c_5391,c_5937])).

cnf(c_48248,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_48239])).

cnf(c_52513,plain,
    ( k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)) = k1_xboole_0
    | r2_hidden(sK0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2,k1_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48248,c_1156])).

cnf(c_150738,plain,
    ( k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))),k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_108802,c_52513])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1158,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1159,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8178,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1159])).

cnf(c_14,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1153,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1152,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1715,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1153,c_1152])).

cnf(c_10326,plain,
    ( k5_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8178,c_1715])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1162,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10333,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X2,X2)
    | r2_hidden(sK1(X2,X2,k1_setfam_1(k2_tarski(X0,X1))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10326,c_1162])).

cnf(c_10332,plain,
    ( k5_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10326,c_4069])).

cnf(c_11678,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) = X0
    | k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_10332])).

cnf(c_10032,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1715,c_16])).

cnf(c_11837,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11678,c_16,c_10032])).

cnf(c_12283,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11837,c_4069])).

cnf(c_12467,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10333,c_12283])).

cnf(c_12471,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12467,c_10032])).

cnf(c_14443,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_12471,c_16])).

cnf(c_150813,plain,
    ( k1_setfam_1(k2_tarski(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_150738,c_12471,c_14443])).

cnf(c_2626,plain,
    ( k5_xboole_0(sK3,k1_setfam_1(k2_tarski(sK3,X0))) = k7_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(superposition,[status(thm)],[c_1150,c_1151])).

cnf(c_150935,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_150813,c_2626])).

cnf(c_151035,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_150935,c_14443])).

cnf(c_158462,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = sK3
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1561,c_151035])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),X0,k2_tops_1(sK2,X0)) = k1_tops_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1149,plain,
    ( k7_subset_1(u1_struct_0(sK2),X0,k2_tops_1(sK2,X0)) = k1_tops_1(sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_1399,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1150,c_1149])).

cnf(c_158578,plain,
    ( k1_tops_1(sK2,sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_158462,c_1399])).

cnf(c_720,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1537,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_2111,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_131209,plain,
    ( k1_tops_1(sK2,sK3) != sK3
    | sK3 = k1_tops_1(sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_725,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_10547,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != k7_subset_1(X1,X3,X5)
    | k7_subset_1(X0,X2,X4) = X6 ),
    inference(resolution,[status(thm)],[c_725,c_720])).

cnf(c_719,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1925,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_720,c_719])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X0),k1_tops_1(sK2,X0)) = k2_tops_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_10761,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tops_1(sK2,X0) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X0),k1_tops_1(sK2,X0)) ),
    inference(resolution,[status(thm)],[c_1925,c_448])).

cnf(c_51829,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 != k1_tops_1(sK2,X0)
    | X2 != k2_pre_topc(sK2,X0)
    | X3 != u1_struct_0(sK2)
    | k7_subset_1(X3,X2,X1) = k2_tops_1(sK2,X0) ),
    inference(resolution,[status(thm)],[c_10547,c_10761])).

cnf(c_716,plain,
    ( sP0_iProver_split
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_536])).

cnf(c_1379,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1373,c_716])).

cnf(c_86343,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != sK3
    | k2_pre_topc(sK2,sK3) != k2_pre_topc(sK2,sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != k1_tops_1(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_51829,c_1379])).

cnf(c_86344,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != sK3
    | sK3 != k1_tops_1(sK2,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_86343])).

cnf(c_1524,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_158578,c_131209,c_86344,c_1524,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:01:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.09/7.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.09/7.48  
% 55.09/7.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.09/7.48  
% 55.09/7.48  ------  iProver source info
% 55.09/7.48  
% 55.09/7.48  git: date: 2020-06-30 10:37:57 +0100
% 55.09/7.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.09/7.48  git: non_committed_changes: false
% 55.09/7.48  git: last_make_outside_of_git: false
% 55.09/7.48  
% 55.09/7.48  ------ 
% 55.09/7.48  ------ Parsing...
% 55.09/7.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.09/7.48  
% 55.09/7.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 55.09/7.48  
% 55.09/7.48  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.09/7.48  
% 55.09/7.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.09/7.48  ------ Proving...
% 55.09/7.48  ------ Problem Properties 
% 55.09/7.48  
% 55.09/7.48  
% 55.09/7.48  clauses                                 25
% 55.09/7.48  conjectures                             1
% 55.09/7.48  EPR                                     2
% 55.09/7.48  Horn                                    18
% 55.09/7.48  unary                                   3
% 55.09/7.48  binary                                  11
% 55.09/7.48  lits                                    60
% 55.09/7.48  lits eq                                 16
% 55.09/7.48  fd_pure                                 0
% 55.09/7.48  fd_pseudo                               0
% 55.09/7.48  fd_cond                                 0
% 55.09/7.48  fd_pseudo_cond                          7
% 55.09/7.48  AC symbols                              0
% 55.09/7.48  
% 55.09/7.48  ------ Input Options Time Limit: Unbounded
% 55.09/7.48  
% 55.09/7.48  
% 55.09/7.48  ------ 
% 55.09/7.48  Current options:
% 55.09/7.48  ------ 
% 55.09/7.48  
% 55.09/7.48  
% 55.09/7.48  
% 55.09/7.48  
% 55.09/7.48  ------ Proving...
% 55.09/7.48  
% 55.09/7.48  
% 55.09/7.48  % SZS status Theorem for theBenchmark.p
% 55.09/7.48  
% 55.09/7.48  % SZS output start CNFRefutation for theBenchmark.p
% 55.09/7.48  
% 55.09/7.48  fof(f13,conjecture,(
% 55.09/7.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f14,negated_conjecture,(
% 55.09/7.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 55.09/7.48    inference(negated_conjecture,[],[f13])).
% 55.09/7.48  
% 55.09/7.48  fof(f23,plain,(
% 55.09/7.48    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 55.09/7.48    inference(ennf_transformation,[],[f14])).
% 55.09/7.48  
% 55.09/7.48  fof(f24,plain,(
% 55.09/7.48    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 55.09/7.48    inference(flattening,[],[f23])).
% 55.09/7.48  
% 55.09/7.48  fof(f37,plain,(
% 55.09/7.48    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 55.09/7.48    inference(nnf_transformation,[],[f24])).
% 55.09/7.48  
% 55.09/7.48  fof(f38,plain,(
% 55.09/7.48    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 55.09/7.48    inference(flattening,[],[f37])).
% 55.09/7.48  
% 55.09/7.48  fof(f40,plain,(
% 55.09/7.48    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK3),sK3) != k2_tops_1(X0,sK3) | ~v3_pre_topc(sK3,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK3),sK3) = k2_tops_1(X0,sK3) | v3_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 55.09/7.48    introduced(choice_axiom,[])).
% 55.09/7.48  
% 55.09/7.48  fof(f39,plain,(
% 55.09/7.48    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X1),X1) != k2_tops_1(sK2,X1) | ~v3_pre_topc(X1,sK2)) & (k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X1),X1) = k2_tops_1(sK2,X1) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 55.09/7.48    introduced(choice_axiom,[])).
% 55.09/7.48  
% 55.09/7.48  fof(f41,plain,(
% 55.09/7.48    ((k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)) & (k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 55.09/7.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).
% 55.09/7.48  
% 55.09/7.48  fof(f70,plain,(
% 55.09/7.48    k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) | v3_pre_topc(sK3,sK2)),
% 55.09/7.48    inference(cnf_transformation,[],[f41])).
% 55.09/7.48  
% 55.09/7.48  fof(f11,axiom,(
% 55.09/7.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f20,plain,(
% 55.09/7.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 55.09/7.48    inference(ennf_transformation,[],[f11])).
% 55.09/7.48  
% 55.09/7.48  fof(f21,plain,(
% 55.09/7.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 55.09/7.48    inference(flattening,[],[f20])).
% 55.09/7.48  
% 55.09/7.48  fof(f64,plain,(
% 55.09/7.48    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f21])).
% 55.09/7.48  
% 55.09/7.48  fof(f67,plain,(
% 55.09/7.48    v2_pre_topc(sK2)),
% 55.09/7.48    inference(cnf_transformation,[],[f41])).
% 55.09/7.48  
% 55.09/7.48  fof(f68,plain,(
% 55.09/7.48    l1_pre_topc(sK2)),
% 55.09/7.48    inference(cnf_transformation,[],[f41])).
% 55.09/7.48  
% 55.09/7.48  fof(f69,plain,(
% 55.09/7.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 55.09/7.48    inference(cnf_transformation,[],[f41])).
% 55.09/7.48  
% 55.09/7.48  fof(f71,plain,(
% 55.09/7.48    k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)),
% 55.09/7.48    inference(cnf_transformation,[],[f41])).
% 55.09/7.48  
% 55.09/7.48  fof(f65,plain,(
% 55.09/7.48    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f21])).
% 55.09/7.48  
% 55.09/7.48  fof(f1,axiom,(
% 55.09/7.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f25,plain,(
% 55.09/7.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.09/7.48    inference(nnf_transformation,[],[f1])).
% 55.09/7.48  
% 55.09/7.48  fof(f26,plain,(
% 55.09/7.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.09/7.48    inference(flattening,[],[f25])).
% 55.09/7.48  
% 55.09/7.48  fof(f27,plain,(
% 55.09/7.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.09/7.48    inference(rectify,[],[f26])).
% 55.09/7.48  
% 55.09/7.48  fof(f28,plain,(
% 55.09/7.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 55.09/7.48    introduced(choice_axiom,[])).
% 55.09/7.48  
% 55.09/7.48  fof(f29,plain,(
% 55.09/7.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.09/7.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 55.09/7.48  
% 55.09/7.48  fof(f45,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f29])).
% 55.09/7.48  
% 55.09/7.48  fof(f8,axiom,(
% 55.09/7.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f61,plain,(
% 55.09/7.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.09/7.48    inference(cnf_transformation,[],[f8])).
% 55.09/7.48  
% 55.09/7.48  fof(f75,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(definition_unfolding,[],[f45,f61])).
% 55.09/7.48  
% 55.09/7.48  fof(f46,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f29])).
% 55.09/7.48  
% 55.09/7.48  fof(f74,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(definition_unfolding,[],[f46,f61])).
% 55.09/7.48  
% 55.09/7.48  fof(f9,axiom,(
% 55.09/7.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f17,plain,(
% 55.09/7.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 55.09/7.48    inference(ennf_transformation,[],[f9])).
% 55.09/7.48  
% 55.09/7.48  fof(f18,plain,(
% 55.09/7.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 55.09/7.48    inference(flattening,[],[f17])).
% 55.09/7.48  
% 55.09/7.48  fof(f62,plain,(
% 55.09/7.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f18])).
% 55.09/7.48  
% 55.09/7.48  fof(f7,axiom,(
% 55.09/7.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f16,plain,(
% 55.09/7.48    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.09/7.48    inference(ennf_transformation,[],[f7])).
% 55.09/7.48  
% 55.09/7.48  fof(f60,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.09/7.48    inference(cnf_transformation,[],[f16])).
% 55.09/7.48  
% 55.09/7.48  fof(f4,axiom,(
% 55.09/7.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f57,plain,(
% 55.09/7.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.09/7.48    inference(cnf_transformation,[],[f4])).
% 55.09/7.48  
% 55.09/7.48  fof(f72,plain,(
% 55.09/7.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 55.09/7.48    inference(definition_unfolding,[],[f57,f61])).
% 55.09/7.48  
% 55.09/7.48  fof(f87,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.09/7.48    inference(definition_unfolding,[],[f60,f72])).
% 55.09/7.48  
% 55.09/7.48  fof(f2,axiom,(
% 55.09/7.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f30,plain,(
% 55.09/7.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.09/7.48    inference(nnf_transformation,[],[f2])).
% 55.09/7.48  
% 55.09/7.48  fof(f31,plain,(
% 55.09/7.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.09/7.48    inference(flattening,[],[f30])).
% 55.09/7.48  
% 55.09/7.48  fof(f32,plain,(
% 55.09/7.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.09/7.48    inference(rectify,[],[f31])).
% 55.09/7.48  
% 55.09/7.48  fof(f33,plain,(
% 55.09/7.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 55.09/7.48    introduced(choice_axiom,[])).
% 55.09/7.48  
% 55.09/7.48  fof(f34,plain,(
% 55.09/7.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.09/7.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 55.09/7.48  
% 55.09/7.48  fof(f49,plain,(
% 55.09/7.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 55.09/7.48    inference(cnf_transformation,[],[f34])).
% 55.09/7.48  
% 55.09/7.48  fof(f83,plain,(
% 55.09/7.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 55.09/7.48    inference(definition_unfolding,[],[f49,f72])).
% 55.09/7.48  
% 55.09/7.48  fof(f92,plain,(
% 55.09/7.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 55.09/7.48    inference(equality_resolution,[],[f83])).
% 55.09/7.48  
% 55.09/7.48  fof(f6,axiom,(
% 55.09/7.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f59,plain,(
% 55.09/7.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.09/7.48    inference(cnf_transformation,[],[f6])).
% 55.09/7.48  
% 55.09/7.48  fof(f86,plain,(
% 55.09/7.48    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 55.09/7.48    inference(definition_unfolding,[],[f59,f72])).
% 55.09/7.48  
% 55.09/7.48  fof(f47,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f29])).
% 55.09/7.48  
% 55.09/7.48  fof(f73,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(definition_unfolding,[],[f47,f61])).
% 55.09/7.48  
% 55.09/7.48  fof(f51,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f34])).
% 55.09/7.48  
% 55.09/7.48  fof(f81,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(definition_unfolding,[],[f51,f72])).
% 55.09/7.48  
% 55.09/7.48  fof(f52,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f34])).
% 55.09/7.48  
% 55.09/7.48  fof(f80,plain,(
% 55.09/7.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 55.09/7.48    inference(definition_unfolding,[],[f52,f72])).
% 55.09/7.48  
% 55.09/7.48  fof(f3,axiom,(
% 55.09/7.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f35,plain,(
% 55.09/7.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.09/7.48    inference(nnf_transformation,[],[f3])).
% 55.09/7.48  
% 55.09/7.48  fof(f36,plain,(
% 55.09/7.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.09/7.48    inference(flattening,[],[f35])).
% 55.09/7.48  
% 55.09/7.48  fof(f54,plain,(
% 55.09/7.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 55.09/7.48    inference(cnf_transformation,[],[f36])).
% 55.09/7.48  
% 55.09/7.48  fof(f95,plain,(
% 55.09/7.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 55.09/7.48    inference(equality_resolution,[],[f54])).
% 55.09/7.48  
% 55.09/7.48  fof(f5,axiom,(
% 55.09/7.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f15,plain,(
% 55.09/7.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 55.09/7.48    inference(ennf_transformation,[],[f5])).
% 55.09/7.48  
% 55.09/7.48  fof(f58,plain,(
% 55.09/7.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f15])).
% 55.09/7.48  
% 55.09/7.48  fof(f85,plain,(
% 55.09/7.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 55.09/7.48    inference(definition_unfolding,[],[f58,f61])).
% 55.09/7.48  
% 55.09/7.48  fof(f43,plain,(
% 55.09/7.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 55.09/7.48    inference(cnf_transformation,[],[f29])).
% 55.09/7.48  
% 55.09/7.48  fof(f77,plain,(
% 55.09/7.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 55.09/7.48    inference(definition_unfolding,[],[f43,f61])).
% 55.09/7.48  
% 55.09/7.48  fof(f89,plain,(
% 55.09/7.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 55.09/7.48    inference(equality_resolution,[],[f77])).
% 55.09/7.48  
% 55.09/7.48  fof(f12,axiom,(
% 55.09/7.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f22,plain,(
% 55.09/7.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.09/7.48    inference(ennf_transformation,[],[f12])).
% 55.09/7.48  
% 55.09/7.48  fof(f66,plain,(
% 55.09/7.48    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f22])).
% 55.09/7.48  
% 55.09/7.48  fof(f10,axiom,(
% 55.09/7.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 55.09/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.09/7.48  
% 55.09/7.48  fof(f19,plain,(
% 55.09/7.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.09/7.48    inference(ennf_transformation,[],[f10])).
% 55.09/7.48  
% 55.09/7.48  fof(f63,plain,(
% 55.09/7.48    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.09/7.48    inference(cnf_transformation,[],[f19])).
% 55.09/7.48  
% 55.09/7.48  cnf(c_24,negated_conjecture,
% 55.09/7.48      ( v3_pre_topc(sK3,sK2)
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
% 55.09/7.48      inference(cnf_transformation,[],[f70]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_205,plain,
% 55.09/7.48      ( v3_pre_topc(sK3,sK2)
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
% 55.09/7.48      inference(prop_impl,[status(thm)],[c_24]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_21,plain,
% 55.09/7.48      ( ~ v3_pre_topc(X0,X1)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 55.09/7.48      | ~ v2_pre_topc(X3)
% 55.09/7.48      | ~ l1_pre_topc(X3)
% 55.09/7.48      | ~ l1_pre_topc(X1)
% 55.09/7.48      | k1_tops_1(X1,X0) = X0 ),
% 55.09/7.48      inference(cnf_transformation,[],[f64]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_27,negated_conjecture,
% 55.09/7.48      ( v2_pre_topc(sK2) ),
% 55.09/7.48      inference(cnf_transformation,[],[f67]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_380,plain,
% 55.09/7.48      ( ~ v3_pre_topc(X0,X1)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 55.09/7.48      | ~ l1_pre_topc(X1)
% 55.09/7.48      | ~ l1_pre_topc(X3)
% 55.09/7.48      | k1_tops_1(X1,X0) = X0
% 55.09/7.48      | sK2 != X3 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_381,plain,
% 55.09/7.48      ( ~ v3_pre_topc(X0,X1)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ l1_pre_topc(X1)
% 55.09/7.48      | ~ l1_pre_topc(sK2)
% 55.09/7.48      | k1_tops_1(X1,X0) = X0 ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_380]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_26,negated_conjecture,
% 55.09/7.48      ( l1_pre_topc(sK2) ),
% 55.09/7.48      inference(cnf_transformation,[],[f68]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_385,plain,
% 55.09/7.48      ( ~ l1_pre_topc(X1)
% 55.09/7.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ v3_pre_topc(X0,X1)
% 55.09/7.48      | k1_tops_1(X1,X0) = X0 ),
% 55.09/7.48      inference(global_propositional_subsumption,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_381,c_26]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_386,plain,
% 55.09/7.48      ( ~ v3_pre_topc(X0,X1)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ l1_pre_topc(X1)
% 55.09/7.48      | k1_tops_1(X1,X0) = X0 ),
% 55.09/7.48      inference(renaming,[status(thm)],[c_385]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_417,plain,
% 55.09/7.48      ( ~ v3_pre_topc(X0,X1)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k1_tops_1(X1,X0) = X0
% 55.09/7.48      | sK2 != X1 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_386,c_26]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_418,plain,
% 55.09/7.48      ( ~ v3_pre_topc(X0,sK2)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k1_tops_1(sK2,X0) = X0 ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_417]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_510,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,X0) = X0
% 55.09/7.48      | sK3 != X0
% 55.09/7.48      | sK2 != sK2 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_205,c_418]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_511,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) = sK3 ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_510]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_25,negated_conjecture,
% 55.09/7.48      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 55.09/7.48      inference(cnf_transformation,[],[f69]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_515,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) = sK3 ),
% 55.09/7.48      inference(global_propositional_subsumption,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_511,c_25]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_717,plain,
% 55.09/7.48      ( sP0_iProver_split
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) = sK3 ),
% 55.09/7.48      inference(splitting,
% 55.09/7.48                [splitting(split),new_symbols(definition,[])],
% 55.09/7.48                [c_515]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1145,plain,
% 55.09/7.48      ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) = sK3
% 55.09/7.48      | sP0_iProver_split = iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_23,negated_conjecture,
% 55.09/7.48      ( ~ v3_pre_topc(sK3,sK2)
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) ),
% 55.09/7.48      inference(cnf_transformation,[],[f71]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_203,plain,
% 55.09/7.48      ( ~ v3_pre_topc(sK3,sK2)
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) ),
% 55.09/7.48      inference(prop_impl,[status(thm)],[c_23]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_20,plain,
% 55.09/7.48      ( v3_pre_topc(X0,X1)
% 55.09/7.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ v2_pre_topc(X1)
% 55.09/7.48      | ~ l1_pre_topc(X1)
% 55.09/7.48      | ~ l1_pre_topc(X3)
% 55.09/7.48      | k1_tops_1(X1,X0) != X0 ),
% 55.09/7.48      inference(cnf_transformation,[],[f65]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_355,plain,
% 55.09/7.48      ( v3_pre_topc(X0,X1)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 55.09/7.48      | ~ l1_pre_topc(X1)
% 55.09/7.48      | ~ l1_pre_topc(X3)
% 55.09/7.48      | k1_tops_1(X1,X0) != X0
% 55.09/7.48      | sK2 != X1 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_356,plain,
% 55.09/7.48      ( v3_pre_topc(X0,sK2)
% 55.09/7.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ l1_pre_topc(X2)
% 55.09/7.48      | ~ l1_pre_topc(sK2)
% 55.09/7.48      | k1_tops_1(sK2,X0) != X0 ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_355]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_360,plain,
% 55.09/7.48      ( ~ l1_pre_topc(X2)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 55.09/7.48      | v3_pre_topc(X0,sK2)
% 55.09/7.48      | k1_tops_1(sK2,X0) != X0 ),
% 55.09/7.48      inference(global_propositional_subsumption,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_356,c_26]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_361,plain,
% 55.09/7.48      ( v3_pre_topc(X0,sK2)
% 55.09/7.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ l1_pre_topc(X2)
% 55.09/7.48      | k1_tops_1(sK2,X0) != X0 ),
% 55.09/7.48      inference(renaming,[status(thm)],[c_360]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_471,plain,
% 55.09/7.48      ( v3_pre_topc(X0,sK2)
% 55.09/7.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k1_tops_1(sK2,X0) != X0
% 55.09/7.48      | sK2 != X2 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_26,c_361]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_472,plain,
% 55.09/7.48      ( v3_pre_topc(X0,sK2)
% 55.09/7.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k1_tops_1(sK2,X0) != X0 ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_471]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_531,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,X0) != X0
% 55.09/7.48      | sK3 != X0
% 55.09/7.48      | sK2 != sK2 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_203,c_472]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_532,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) != sK3 ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_531]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_536,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) != sK3 ),
% 55.09/7.48      inference(global_propositional_subsumption,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_532,c_25]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_715,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | ~ sP0_iProver_split ),
% 55.09/7.48      inference(splitting,
% 55.09/7.48                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 55.09/7.48                [c_536]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1373,plain,
% 55.09/7.48      ( ~ sP0_iProver_split ),
% 55.09/7.48      inference(resolution,[status(thm)],[c_715,c_25]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1560,plain,
% 55.09/7.48      ( k1_tops_1(sK2,sK3) = sK3
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
% 55.09/7.48      inference(global_propositional_subsumption,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_1145,c_717,c_1373]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1561,plain,
% 55.09/7.48      ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) = sK3 ),
% 55.09/7.48      inference(renaming,[status(thm)],[c_1560]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_2,plain,
% 55.09/7.48      ( r2_hidden(sK0(X0,X1,X2),X0)
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 55.09/7.48      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 55.09/7.48      inference(cnf_transformation,[],[f75]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1164,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1,plain,
% 55.09/7.48      ( r2_hidden(sK0(X0,X1,X2),X1)
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 55.09/7.48      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 55.09/7.48      inference(cnf_transformation,[],[f74]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1165,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1150,plain,
% 55.09/7.48      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_18,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ l1_pre_topc(X1) ),
% 55.09/7.48      inference(cnf_transformation,[],[f62]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_459,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | sK2 != X1 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_460,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_459]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1147,plain,
% 55.09/7.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 55.09/7.48      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_17,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.09/7.48      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 55.09/7.48      inference(cnf_transformation,[],[f87]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1151,plain,
% 55.09/7.48      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 55.09/7.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_2627,plain,
% 55.09/7.48      ( k5_xboole_0(k2_pre_topc(sK2,X0),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,X0),X1))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X0),X1)
% 55.09/7.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1147,c_1151]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_3447,plain,
% 55.09/7.48      ( k5_xboole_0(k2_pre_topc(sK2,sK3),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,sK3),X0))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0) ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1150,c_2627]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_10,plain,
% 55.09/7.48      ( ~ r2_hidden(X0,X1)
% 55.09/7.48      | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
% 55.09/7.48      inference(cnf_transformation,[],[f92]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1156,plain,
% 55.09/7.48      ( r2_hidden(X0,X1) != iProver_top
% 55.09/7.48      | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) != iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_4071,plain,
% 55.09/7.48      ( r2_hidden(X0,X1) != iProver_top
% 55.09/7.48      | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1)) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_3447,c_1156]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_5932,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1))) = X2
% 55.09/7.48      | r2_hidden(sK0(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1),X2),X1) != iProver_top
% 55.09/7.48      | r2_hidden(sK0(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1),X2),X2) = iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1165,c_4071]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_108802,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0))) = X1
% 55.09/7.48      | r2_hidden(sK0(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0),X1),X1) = iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1164,c_5932]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_16,plain,
% 55.09/7.48      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 55.09/7.48      inference(cnf_transformation,[],[f86]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_4069,plain,
% 55.09/7.48      ( r2_hidden(X0,X1) != iProver_top
% 55.09/7.48      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_16,c_1156]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_5377,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1164,c_4069]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_0,plain,
% 55.09/7.48      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 55.09/7.48      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 55.09/7.48      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 55.09/7.48      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 55.09/7.48      inference(cnf_transformation,[],[f73]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_85,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_5391,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1164,c_4069]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_5937,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1165,c_4069]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_48239,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 55.09/7.48      | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 55.09/7.48      inference(global_propositional_subsumption,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_5377,c_85,c_5391,c_5937]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_48248,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 55.09/7.48      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1164,c_48239]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_52513,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)) = k1_xboole_0
% 55.09/7.48      | r2_hidden(sK0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2,k1_xboole_0),X1) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_48248,c_1156]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_150738,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))),k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))))) = k1_xboole_0 ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_108802,c_52513]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_8,plain,
% 55.09/7.48      ( r2_hidden(sK1(X0,X1,X2),X0)
% 55.09/7.48      | r2_hidden(sK1(X0,X1,X2),X2)
% 55.09/7.48      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ),
% 55.09/7.48      inference(cnf_transformation,[],[f81]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1158,plain,
% 55.09/7.48      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
% 55.09/7.48      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 55.09/7.48      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_7,plain,
% 55.09/7.48      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 55.09/7.48      | r2_hidden(sK1(X0,X1,X2),X2)
% 55.09/7.48      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ),
% 55.09/7.48      inference(cnf_transformation,[],[f80]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1159,plain,
% 55.09/7.48      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
% 55.09/7.48      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 55.09/7.48      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_8178,plain,
% 55.09/7.48      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1
% 55.09/7.48      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1158,c_1159]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_14,plain,
% 55.09/7.48      ( r1_tarski(X0,X0) ),
% 55.09/7.48      inference(cnf_transformation,[],[f95]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1153,plain,
% 55.09/7.48      ( r1_tarski(X0,X0) = iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_15,plain,
% 55.09/7.48      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 55.09/7.48      inference(cnf_transformation,[],[f85]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1152,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 55.09/7.48      | r1_tarski(X0,X1) != iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1715,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1153,c_1152]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_10326,plain,
% 55.09/7.48      ( k5_xboole_0(X0,X0) = X1
% 55.09/7.48      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 55.09/7.48      inference(light_normalisation,[status(thm)],[c_8178,c_1715]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_4,plain,
% 55.09/7.48      ( r2_hidden(X0,X1)
% 55.09/7.48      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 55.09/7.48      inference(cnf_transformation,[],[f89]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1162,plain,
% 55.09/7.48      ( r2_hidden(X0,X1) = iProver_top
% 55.09/7.48      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_10333,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X2,X2)
% 55.09/7.48      | r2_hidden(sK1(X2,X2,k1_setfam_1(k2_tarski(X0,X1))),X1) = iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_10326,c_1162]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_10332,plain,
% 55.09/7.48      ( k5_xboole_0(X0,X0) = X1
% 55.09/7.48      | r2_hidden(sK1(X0,X0,X1),k1_xboole_0) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_10326,c_4069]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_11678,plain,
% 55.09/7.48      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) = X0
% 55.09/7.48      | k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0
% 55.09/7.48      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1158,c_10332]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_10032,plain,
% 55.09/7.48      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1715,c_16]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_11837,plain,
% 55.09/7.48      ( k1_xboole_0 = X0
% 55.09/7.48      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
% 55.09/7.48      inference(demodulation,[status(thm)],[c_11678,c_16,c_10032]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_12283,plain,
% 55.09/7.48      ( k1_xboole_0 = X0
% 55.09/7.48      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_11837,c_4069]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_12467,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 55.09/7.48      | k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_10333,c_12283]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_12471,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.09/7.48      inference(light_normalisation,[status(thm)],[c_12467,c_10032]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_14443,plain,
% 55.09/7.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.09/7.48      inference(demodulation,[status(thm)],[c_12471,c_16]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_150813,plain,
% 55.09/7.48      ( k1_setfam_1(k2_tarski(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0))) = k1_xboole_0 ),
% 55.09/7.48      inference(light_normalisation,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_150738,c_12471,c_14443]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_2626,plain,
% 55.09/7.48      ( k5_xboole_0(sK3,k1_setfam_1(k2_tarski(sK3,X0))) = k7_subset_1(u1_struct_0(sK2),sK3,X0) ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1150,c_1151]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_150935,plain,
% 55.09/7.48      ( k7_subset_1(u1_struct_0(sK2),sK3,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_150813,c_2626]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_151035,plain,
% 55.09/7.48      ( k7_subset_1(u1_struct_0(sK2),sK3,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3)) = sK3 ),
% 55.09/7.48      inference(demodulation,[status(thm)],[c_150935,c_14443]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_158462,plain,
% 55.09/7.48      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = sK3
% 55.09/7.48      | k1_tops_1(sK2,sK3) = sK3 ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1561,c_151035]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_22,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ l1_pre_topc(X1)
% 55.09/7.48      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 55.09/7.48      inference(cnf_transformation,[],[f66]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_435,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 55.09/7.48      | sK2 != X1 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_436,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),X0,k2_tops_1(sK2,X0)) = k1_tops_1(sK2,X0) ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_435]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1149,plain,
% 55.09/7.48      ( k7_subset_1(u1_struct_0(sK2),X0,k2_tops_1(sK2,X0)) = k1_tops_1(sK2,X0)
% 55.09/7.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 55.09/7.48      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1399,plain,
% 55.09/7.48      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
% 55.09/7.48      inference(superposition,[status(thm)],[c_1150,c_1149]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_158578,plain,
% 55.09/7.48      ( k1_tops_1(sK2,sK3) = sK3 ),
% 55.09/7.48      inference(demodulation,[status(thm)],[c_158462,c_1399]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_720,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1537,plain,
% 55.09/7.48      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 55.09/7.48      inference(instantiation,[status(thm)],[c_720]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_2111,plain,
% 55.09/7.48      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 55.09/7.48      inference(instantiation,[status(thm)],[c_1537]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_131209,plain,
% 55.09/7.48      ( k1_tops_1(sK2,sK3) != sK3
% 55.09/7.48      | sK3 = k1_tops_1(sK2,sK3)
% 55.09/7.48      | sK3 != sK3 ),
% 55.09/7.48      inference(instantiation,[status(thm)],[c_2111]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_725,plain,
% 55.09/7.48      ( X0 != X1
% 55.09/7.48      | X2 != X3
% 55.09/7.48      | X4 != X5
% 55.09/7.48      | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
% 55.09/7.48      theory(equality) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_10547,plain,
% 55.09/7.48      ( X0 != X1
% 55.09/7.48      | X2 != X3
% 55.09/7.48      | X4 != X5
% 55.09/7.48      | X6 != k7_subset_1(X1,X3,X5)
% 55.09/7.48      | k7_subset_1(X0,X2,X4) = X6 ),
% 55.09/7.48      inference(resolution,[status(thm)],[c_725,c_720]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_719,plain,( X0 = X0 ),theory(equality) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1925,plain,
% 55.09/7.48      ( X0 != X1 | X1 = X0 ),
% 55.09/7.48      inference(resolution,[status(thm)],[c_720,c_719]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_19,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | ~ l1_pre_topc(X1)
% 55.09/7.48      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 55.09/7.48      inference(cnf_transformation,[],[f63]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_447,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 55.09/7.48      | sK2 != X1 ),
% 55.09/7.48      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_448,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X0),k1_tops_1(sK2,X0)) = k2_tops_1(sK2,X0) ),
% 55.09/7.48      inference(unflattening,[status(thm)],[c_447]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_10761,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k2_tops_1(sK2,X0) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X0),k1_tops_1(sK2,X0)) ),
% 55.09/7.48      inference(resolution,[status(thm)],[c_1925,c_448]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_51829,plain,
% 55.09/7.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | X1 != k1_tops_1(sK2,X0)
% 55.09/7.48      | X2 != k2_pre_topc(sK2,X0)
% 55.09/7.48      | X3 != u1_struct_0(sK2)
% 55.09/7.48      | k7_subset_1(X3,X2,X1) = k2_tops_1(sK2,X0) ),
% 55.09/7.48      inference(resolution,[status(thm)],[c_10547,c_10761]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_716,plain,
% 55.09/7.48      ( sP0_iProver_split
% 55.09/7.48      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) != sK3 ),
% 55.09/7.48      inference(splitting,
% 55.09/7.48                [splitting(split),new_symbols(definition,[])],
% 55.09/7.48                [c_536]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1379,plain,
% 55.09/7.48      ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
% 55.09/7.48      | k1_tops_1(sK2,sK3) != sK3 ),
% 55.09/7.48      inference(backward_subsumption_resolution,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_1373,c_716]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_86343,plain,
% 55.09/7.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k1_tops_1(sK2,sK3) != sK3
% 55.09/7.48      | k2_pre_topc(sK2,sK3) != k2_pre_topc(sK2,sK3)
% 55.09/7.48      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 55.09/7.48      | sK3 != k1_tops_1(sK2,sK3) ),
% 55.09/7.48      inference(resolution,[status(thm)],[c_51829,c_1379]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_86344,plain,
% 55.09/7.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 55.09/7.48      | k1_tops_1(sK2,sK3) != sK3
% 55.09/7.48      | sK3 != k1_tops_1(sK2,sK3) ),
% 55.09/7.48      inference(equality_resolution_simp,[status(thm)],[c_86343]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(c_1524,plain,
% 55.09/7.48      ( sK3 = sK3 ),
% 55.09/7.48      inference(instantiation,[status(thm)],[c_719]) ).
% 55.09/7.48  
% 55.09/7.48  cnf(contradiction,plain,
% 55.09/7.48      ( $false ),
% 55.09/7.48      inference(minisat,
% 55.09/7.48                [status(thm)],
% 55.09/7.48                [c_158578,c_131209,c_86344,c_1524,c_25]) ).
% 55.09/7.48  
% 55.09/7.48  
% 55.09/7.48  % SZS output end CNFRefutation for theBenchmark.p
% 55.09/7.48  
% 55.09/7.48  ------                               Statistics
% 55.09/7.48  
% 55.09/7.48  ------ Selected
% 55.09/7.48  
% 55.09/7.48  total_time:                             6.51
% 55.09/7.48  
%------------------------------------------------------------------------------

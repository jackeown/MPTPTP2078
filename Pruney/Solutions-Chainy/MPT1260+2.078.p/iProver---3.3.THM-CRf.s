%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:24 EST 2020

% Result     : Theorem 47.95s
% Output     : CNFRefutation 47.95s
% Verified   : 
% Statistics : Number of formulae       :  167 (2088 expanded)
%              Number of clauses        :   96 ( 504 expanded)
%              Number of leaves         :   18 ( 481 expanded)
%              Depth                    :   26
%              Number of atoms          :  610 (10346 expanded)
%              Number of equality atoms :  234 (3026 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
    ( ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
      | ~ v3_pre_topc(sK3,sK2) )
    & ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_897,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_898,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2727,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_898])).

cnf(c_12,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2743,plain,
    ( k5_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2727,c_12])).

cnf(c_20,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_882,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | v3_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_881,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_261,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_17])).

cnf(c_886,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_1706,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | v3_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_886])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_262,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_17])).

cnf(c_301,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_17])).

cnf(c_887,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_2182,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_887])).

cnf(c_3749,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1706,c_24,c_25,c_301,c_2182])).

cnf(c_3755,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_882,c_3749])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_892,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_893,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1805,plain,
    ( k5_xboole_0(k2_pre_topc(X0,X1),k1_setfam_1(k2_tarski(k2_pre_topc(X0,X1),X2))) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_893])).

cnf(c_5008,plain,
    ( k5_xboole_0(k2_pre_topc(sK2,sK3),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,sK3),X0))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_1805])).

cnf(c_1142,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1263,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | k5_xboole_0(k2_pre_topc(sK2,sK3),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,sK3),X0))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8628,plain,
    ( k5_xboole_0(k2_pre_topc(sK2,sK3),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,sK3),X0))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5008,c_22,c_21,c_1142,c_1263])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_895,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8638,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8628,c_895])).

cnf(c_8957,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | r2_hidden(X0,k2_tops_1(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3755,c_8638])).

cnf(c_145359,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | k5_xboole_0(X0,X0) = k2_tops_1(sK2,sK3)
    | r2_hidden(sK1(X0,X0,k2_tops_1(sK2,sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_8957])).

cnf(c_1707,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ sP1_iProver_split
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1706])).

cnf(c_2189,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2182])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_267,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3797,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_274,c_267])).

cnf(c_273,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_13487,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(X0),X1)
    | m1_subset_1(k1_zfmisc_1(X2),X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_3797,c_273])).

cnf(c_142731,plain,
    ( v3_pre_topc(sK3,sK2)
    | m1_subset_1(k1_zfmisc_1(k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3)),X0)
    | ~ m1_subset_1(k1_zfmisc_1(k2_tops_1(sK2,sK3)),X0) ),
    inference(resolution,[status(thm)],[c_13487,c_20])).

cnf(c_16,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_264,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_16])).

cnf(c_265,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_16])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_16])).

cnf(c_543,plain,
    ( k1_tops_1(X1,X0) != X0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_265,c_263])).

cnf(c_544,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_1187,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_884,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2290,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_884])).

cnf(c_1184,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4326,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2290,c_22,c_21,c_1184])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_904,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1582,plain,
    ( k5_xboole_0(sK3,k1_setfam_1(k2_tarski(sK3,X0))) = k7_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(superposition,[status(thm)],[c_881,c_893])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_894,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3646,plain,
    ( r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),sK3,X1)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_894])).

cnf(c_3929,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(sK0(X1,X2,k7_subset_1(u1_struct_0(sK2),sK3,X0)),X2) = iProver_top
    | r2_hidden(sK0(X1,X2,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_3646])).

cnf(c_8847,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(X1,sK3))
    | r2_hidden(sK0(X1,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3929])).

cnf(c_8849,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(X1,sK3))
    | r2_hidden(sK0(X1,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8847])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_905,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_115476,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(sK3,sK3))
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),k7_subset_1(u1_struct_0(sK2),sK3,X0)) != iProver_top
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8849,c_905])).

cnf(c_115495,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(sK3,sK3))
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),k7_subset_1(u1_struct_0(sK2),sK3,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_115476,c_8849])).

cnf(c_115496,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),k7_subset_1(u1_struct_0(sK2),sK3,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_115495,c_12])).

cnf(c_116226,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(sK3,sK3))
    | k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_115496])).

cnf(c_116255,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_116226,c_12])).

cnf(c_116877,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = sK3
    | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4326,c_116255])).

cnf(c_116895,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_116877,c_4326])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_896,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3645,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),sK3,X1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_896])).

cnf(c_116228,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),X0) = iProver_top
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3645,c_115496])).

cnf(c_116258,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),X0) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_116255,c_116228])).

cnf(c_145447,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = sK3
    | k1_tops_1(sK2,sK3) = sK3
    | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_116258,c_8957])).

cnf(c_145486,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = sK3
    | k1_tops_1(sK2,sK3) = sK3
    | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_145447,c_4326])).

cnf(c_145487,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_145486,c_4326])).

cnf(c_146890,plain,
    ( v3_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_142731,c_23,c_22,c_21,c_1187,c_116895,c_145487])).

cnf(c_152069,plain,
    ( k1_tops_1(sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_145359,c_116895,c_145487])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_891,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3017,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k1_tops_1(sK2,sK3)) = k2_tops_1(sK2,sK3)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_891])).

cnf(c_1190,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k1_tops_1(sK2,sK3)) = k2_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5390,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k1_tops_1(sK2,sK3)) = k2_tops_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3017,c_22,c_21,c_1190])).

cnf(c_152094,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_152069,c_5390])).

cnf(c_19,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_152094,c_146890,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : iproveropt_run.sh %d %s
% 0.08/0.27  % Computer   : n011.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 14:54:27 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.27  % Running in FOF mode
% 47.95/6.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.95/6.49  
% 47.95/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.95/6.49  
% 47.95/6.49  ------  iProver source info
% 47.95/6.49  
% 47.95/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.95/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.95/6.49  git: non_committed_changes: false
% 47.95/6.49  git: last_make_outside_of_git: false
% 47.95/6.49  
% 47.95/6.49  ------ 
% 47.95/6.49  
% 47.95/6.49  ------ Input Options
% 47.95/6.49  
% 47.95/6.49  --out_options                           all
% 47.95/6.49  --tptp_safe_out                         true
% 47.95/6.49  --problem_path                          ""
% 47.95/6.49  --include_path                          ""
% 47.95/6.49  --clausifier                            res/vclausify_rel
% 47.95/6.49  --clausifier_options                    --mode clausify
% 47.95/6.49  --stdin                                 false
% 47.95/6.49  --stats_out                             sel
% 47.95/6.49  
% 47.95/6.49  ------ General Options
% 47.95/6.49  
% 47.95/6.49  --fof                                   false
% 47.95/6.49  --time_out_real                         604.96
% 47.95/6.49  --time_out_virtual                      -1.
% 47.95/6.49  --symbol_type_check                     false
% 47.95/6.49  --clausify_out                          false
% 47.95/6.49  --sig_cnt_out                           false
% 47.95/6.49  --trig_cnt_out                          false
% 47.95/6.49  --trig_cnt_out_tolerance                1.
% 47.95/6.49  --trig_cnt_out_sk_spl                   false
% 47.95/6.49  --abstr_cl_out                          false
% 47.95/6.49  
% 47.95/6.49  ------ Global Options
% 47.95/6.49  
% 47.95/6.49  --schedule                              none
% 47.95/6.49  --add_important_lit                     false
% 47.95/6.49  --prop_solver_per_cl                    1000
% 47.95/6.49  --min_unsat_core                        false
% 47.95/6.49  --soft_assumptions                      false
% 47.95/6.49  --soft_lemma_size                       3
% 47.95/6.49  --prop_impl_unit_size                   0
% 47.95/6.49  --prop_impl_unit                        []
% 47.95/6.49  --share_sel_clauses                     true
% 47.95/6.49  --reset_solvers                         false
% 47.95/6.49  --bc_imp_inh                            [conj_cone]
% 47.95/6.49  --conj_cone_tolerance                   3.
% 47.95/6.49  --extra_neg_conj                        none
% 47.95/6.49  --large_theory_mode                     true
% 47.95/6.49  --prolific_symb_bound                   200
% 47.95/6.49  --lt_threshold                          2000
% 47.95/6.49  --clause_weak_htbl                      true
% 47.95/6.49  --gc_record_bc_elim                     false
% 47.95/6.49  
% 47.95/6.49  ------ Preprocessing Options
% 47.95/6.49  
% 47.95/6.49  --preprocessing_flag                    true
% 47.95/6.49  --time_out_prep_mult                    0.1
% 47.95/6.49  --splitting_mode                        input
% 47.95/6.49  --splitting_grd                         true
% 47.95/6.49  --splitting_cvd                         false
% 47.95/6.49  --splitting_cvd_svl                     false
% 47.95/6.49  --splitting_nvd                         32
% 47.95/6.49  --sub_typing                            true
% 47.95/6.49  --prep_gs_sim                           false
% 47.95/6.49  --prep_unflatten                        true
% 47.95/6.49  --prep_res_sim                          true
% 47.95/6.49  --prep_upred                            true
% 47.95/6.49  --prep_sem_filter                       exhaustive
% 47.95/6.49  --prep_sem_filter_out                   false
% 47.95/6.49  --pred_elim                             false
% 47.95/6.49  --res_sim_input                         true
% 47.95/6.49  --eq_ax_congr_red                       true
% 47.95/6.49  --pure_diseq_elim                       true
% 47.95/6.49  --brand_transform                       false
% 47.95/6.49  --non_eq_to_eq                          false
% 47.95/6.49  --prep_def_merge                        true
% 47.95/6.49  --prep_def_merge_prop_impl              false
% 47.95/6.49  --prep_def_merge_mbd                    true
% 47.95/6.49  --prep_def_merge_tr_red                 false
% 47.95/6.49  --prep_def_merge_tr_cl                  false
% 47.95/6.49  --smt_preprocessing                     true
% 47.95/6.49  --smt_ac_axioms                         fast
% 47.95/6.49  --preprocessed_out                      false
% 47.95/6.49  --preprocessed_stats                    false
% 47.95/6.49  
% 47.95/6.49  ------ Abstraction refinement Options
% 47.95/6.49  
% 47.95/6.49  --abstr_ref                             []
% 47.95/6.49  --abstr_ref_prep                        false
% 47.95/6.49  --abstr_ref_until_sat                   false
% 47.95/6.49  --abstr_ref_sig_restrict                funpre
% 47.95/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.95/6.49  --abstr_ref_under                       []
% 47.95/6.49  
% 47.95/6.49  ------ SAT Options
% 47.95/6.49  
% 47.95/6.49  --sat_mode                              false
% 47.95/6.49  --sat_fm_restart_options                ""
% 47.95/6.49  --sat_gr_def                            false
% 47.95/6.49  --sat_epr_types                         true
% 47.95/6.49  --sat_non_cyclic_types                  false
% 47.95/6.49  --sat_finite_models                     false
% 47.95/6.49  --sat_fm_lemmas                         false
% 47.95/6.49  --sat_fm_prep                           false
% 47.95/6.49  --sat_fm_uc_incr                        true
% 47.95/6.49  --sat_out_model                         small
% 47.95/6.49  --sat_out_clauses                       false
% 47.95/6.49  
% 47.95/6.49  ------ QBF Options
% 47.95/6.49  
% 47.95/6.49  --qbf_mode                              false
% 47.95/6.49  --qbf_elim_univ                         false
% 47.95/6.49  --qbf_dom_inst                          none
% 47.95/6.49  --qbf_dom_pre_inst                      false
% 47.95/6.49  --qbf_sk_in                             false
% 47.95/6.49  --qbf_pred_elim                         true
% 47.95/6.49  --qbf_split                             512
% 47.95/6.49  
% 47.95/6.49  ------ BMC1 Options
% 47.95/6.49  
% 47.95/6.49  --bmc1_incremental                      false
% 47.95/6.49  --bmc1_axioms                           reachable_all
% 47.95/6.49  --bmc1_min_bound                        0
% 47.95/6.49  --bmc1_max_bound                        -1
% 47.95/6.49  --bmc1_max_bound_default                -1
% 47.95/6.49  --bmc1_symbol_reachability              true
% 47.95/6.49  --bmc1_property_lemmas                  false
% 47.95/6.49  --bmc1_k_induction                      false
% 47.95/6.49  --bmc1_non_equiv_states                 false
% 47.95/6.49  --bmc1_deadlock                         false
% 47.95/6.49  --bmc1_ucm                              false
% 47.95/6.49  --bmc1_add_unsat_core                   none
% 47.95/6.49  --bmc1_unsat_core_children              false
% 47.95/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.95/6.49  --bmc1_out_stat                         full
% 47.95/6.49  --bmc1_ground_init                      false
% 47.95/6.49  --bmc1_pre_inst_next_state              false
% 47.95/6.49  --bmc1_pre_inst_state                   false
% 47.95/6.49  --bmc1_pre_inst_reach_state             false
% 47.95/6.49  --bmc1_out_unsat_core                   false
% 47.95/6.49  --bmc1_aig_witness_out                  false
% 47.95/6.49  --bmc1_verbose                          false
% 47.95/6.49  --bmc1_dump_clauses_tptp                false
% 47.95/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.95/6.49  --bmc1_dump_file                        -
% 47.95/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.95/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.95/6.49  --bmc1_ucm_extend_mode                  1
% 47.95/6.49  --bmc1_ucm_init_mode                    2
% 47.95/6.49  --bmc1_ucm_cone_mode                    none
% 47.95/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.95/6.49  --bmc1_ucm_relax_model                  4
% 47.95/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.95/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.95/6.49  --bmc1_ucm_layered_model                none
% 47.95/6.49  --bmc1_ucm_max_lemma_size               10
% 47.95/6.49  
% 47.95/6.49  ------ AIG Options
% 47.95/6.49  
% 47.95/6.49  --aig_mode                              false
% 47.95/6.49  
% 47.95/6.49  ------ Instantiation Options
% 47.95/6.49  
% 47.95/6.49  --instantiation_flag                    true
% 47.95/6.49  --inst_sos_flag                         false
% 47.95/6.49  --inst_sos_phase                        true
% 47.95/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.95/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.95/6.49  --inst_lit_sel_side                     num_symb
% 47.95/6.49  --inst_solver_per_active                1400
% 47.95/6.49  --inst_solver_calls_frac                1.
% 47.95/6.49  --inst_passive_queue_type               priority_queues
% 47.95/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.95/6.49  --inst_passive_queues_freq              [25;2]
% 47.95/6.49  --inst_dismatching                      true
% 47.95/6.49  --inst_eager_unprocessed_to_passive     true
% 47.95/6.49  --inst_prop_sim_given                   true
% 47.95/6.49  --inst_prop_sim_new                     false
% 47.95/6.49  --inst_subs_new                         false
% 47.95/6.49  --inst_eq_res_simp                      false
% 47.95/6.49  --inst_subs_given                       false
% 47.95/6.49  --inst_orphan_elimination               true
% 47.95/6.49  --inst_learning_loop_flag               true
% 47.95/6.49  --inst_learning_start                   3000
% 47.95/6.49  --inst_learning_factor                  2
% 47.95/6.49  --inst_start_prop_sim_after_learn       3
% 47.95/6.49  --inst_sel_renew                        solver
% 47.95/6.49  --inst_lit_activity_flag                true
% 47.95/6.49  --inst_restr_to_given                   false
% 47.95/6.49  --inst_activity_threshold               500
% 47.95/6.49  --inst_out_proof                        true
% 47.95/6.49  
% 47.95/6.49  ------ Resolution Options
% 47.95/6.49  
% 47.95/6.49  --resolution_flag                       true
% 47.95/6.49  --res_lit_sel                           adaptive
% 47.95/6.49  --res_lit_sel_side                      none
% 47.95/6.49  --res_ordering                          kbo
% 47.95/6.49  --res_to_prop_solver                    active
% 47.95/6.49  --res_prop_simpl_new                    false
% 47.95/6.49  --res_prop_simpl_given                  true
% 47.95/6.49  --res_passive_queue_type                priority_queues
% 47.95/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.95/6.49  --res_passive_queues_freq               [15;5]
% 47.95/6.49  --res_forward_subs                      full
% 47.95/6.49  --res_backward_subs                     full
% 47.95/6.49  --res_forward_subs_resolution           true
% 47.95/6.49  --res_backward_subs_resolution          true
% 47.95/6.49  --res_orphan_elimination                true
% 47.95/6.49  --res_time_limit                        2.
% 47.95/6.49  --res_out_proof                         true
% 47.95/6.49  
% 47.95/6.49  ------ Superposition Options
% 47.95/6.49  
% 47.95/6.49  --superposition_flag                    true
% 47.95/6.49  --sup_passive_queue_type                priority_queues
% 47.95/6.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.95/6.49  --sup_passive_queues_freq               [1;4]
% 47.95/6.49  --demod_completeness_check              fast
% 47.95/6.49  --demod_use_ground                      true
% 47.95/6.49  --sup_to_prop_solver                    passive
% 47.95/6.49  --sup_prop_simpl_new                    true
% 47.95/6.49  --sup_prop_simpl_given                  true
% 47.95/6.49  --sup_fun_splitting                     false
% 47.95/6.49  --sup_smt_interval                      50000
% 47.95/6.49  
% 47.95/6.49  ------ Superposition Simplification Setup
% 47.95/6.49  
% 47.95/6.49  --sup_indices_passive                   []
% 47.95/6.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.95/6.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.95/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.95/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.95/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.95/6.49  --sup_full_bw                           [BwDemod]
% 47.95/6.49  --sup_immed_triv                        [TrivRules]
% 47.95/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.95/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.95/6.49  --sup_immed_bw_main                     []
% 47.95/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.95/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.95/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.95/6.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.95/6.49  
% 47.95/6.49  ------ Combination Options
% 47.95/6.49  
% 47.95/6.49  --comb_res_mult                         3
% 47.95/6.49  --comb_sup_mult                         2
% 47.95/6.49  --comb_inst_mult                        10
% 47.95/6.49  
% 47.95/6.49  ------ Debug Options
% 47.95/6.49  
% 47.95/6.49  --dbg_backtrace                         false
% 47.95/6.49  --dbg_dump_prop_clauses                 false
% 47.95/6.49  --dbg_dump_prop_clauses_file            -
% 47.95/6.49  --dbg_out_stat                          false
% 47.95/6.49  ------ Parsing...
% 47.95/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.95/6.49  
% 47.95/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 47.95/6.49  
% 47.95/6.49  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.95/6.49  
% 47.95/6.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.95/6.49  ------ Proving...
% 47.95/6.49  ------ Problem Properties 
% 47.95/6.49  
% 47.95/6.49  
% 47.95/6.49  clauses                                 28
% 47.95/6.49  conjectures                             5
% 47.95/6.49  EPR                                     4
% 47.95/6.49  Horn                                    19
% 47.95/6.49  unary                                   4
% 47.95/6.49  binary                                  9
% 47.95/6.49  lits                                    75
% 47.95/6.49  lits eq                                 14
% 47.95/6.49  fd_pure                                 0
% 47.95/6.49  fd_pseudo                               0
% 47.95/6.49  fd_cond                                 0
% 47.95/6.49  fd_pseudo_cond                          6
% 47.95/6.49  AC symbols                              0
% 47.95/6.49  
% 47.95/6.49  ------ Input Options Time Limit: Unbounded
% 47.95/6.49  
% 47.95/6.49  
% 47.95/6.49  ------ 
% 47.95/6.49  Current options:
% 47.95/6.49  ------ 
% 47.95/6.49  
% 47.95/6.49  ------ Input Options
% 47.95/6.49  
% 47.95/6.49  --out_options                           all
% 47.95/6.49  --tptp_safe_out                         true
% 47.95/6.49  --problem_path                          ""
% 47.95/6.49  --include_path                          ""
% 47.95/6.49  --clausifier                            res/vclausify_rel
% 47.95/6.49  --clausifier_options                    --mode clausify
% 47.95/6.49  --stdin                                 false
% 47.95/6.49  --stats_out                             sel
% 47.95/6.49  
% 47.95/6.49  ------ General Options
% 47.95/6.49  
% 47.95/6.49  --fof                                   false
% 47.95/6.49  --time_out_real                         604.96
% 47.95/6.49  --time_out_virtual                      -1.
% 47.95/6.49  --symbol_type_check                     false
% 47.95/6.49  --clausify_out                          false
% 47.95/6.49  --sig_cnt_out                           false
% 47.95/6.49  --trig_cnt_out                          false
% 47.95/6.49  --trig_cnt_out_tolerance                1.
% 47.95/6.49  --trig_cnt_out_sk_spl                   false
% 47.95/6.49  --abstr_cl_out                          false
% 47.95/6.49  
% 47.95/6.49  ------ Global Options
% 47.95/6.49  
% 47.95/6.49  --schedule                              none
% 47.95/6.49  --add_important_lit                     false
% 47.95/6.49  --prop_solver_per_cl                    1000
% 47.95/6.49  --min_unsat_core                        false
% 47.95/6.49  --soft_assumptions                      false
% 47.95/6.49  --soft_lemma_size                       3
% 47.95/6.49  --prop_impl_unit_size                   0
% 47.95/6.49  --prop_impl_unit                        []
% 47.95/6.49  --share_sel_clauses                     true
% 47.95/6.49  --reset_solvers                         false
% 47.95/6.49  --bc_imp_inh                            [conj_cone]
% 47.95/6.49  --conj_cone_tolerance                   3.
% 47.95/6.49  --extra_neg_conj                        none
% 47.95/6.49  --large_theory_mode                     true
% 47.95/6.49  --prolific_symb_bound                   200
% 47.95/6.49  --lt_threshold                          2000
% 47.95/6.49  --clause_weak_htbl                      true
% 47.95/6.49  --gc_record_bc_elim                     false
% 47.95/6.49  
% 47.95/6.49  ------ Preprocessing Options
% 47.95/6.49  
% 47.95/6.49  --preprocessing_flag                    true
% 47.95/6.49  --time_out_prep_mult                    0.1
% 47.95/6.49  --splitting_mode                        input
% 47.95/6.49  --splitting_grd                         true
% 47.95/6.49  --splitting_cvd                         false
% 47.95/6.49  --splitting_cvd_svl                     false
% 47.95/6.49  --splitting_nvd                         32
% 47.95/6.49  --sub_typing                            true
% 47.95/6.49  --prep_gs_sim                           false
% 47.95/6.49  --prep_unflatten                        true
% 47.95/6.49  --prep_res_sim                          true
% 47.95/6.49  --prep_upred                            true
% 47.95/6.49  --prep_sem_filter                       exhaustive
% 47.95/6.49  --prep_sem_filter_out                   false
% 47.95/6.49  --pred_elim                             false
% 47.95/6.49  --res_sim_input                         true
% 47.95/6.49  --eq_ax_congr_red                       true
% 47.95/6.49  --pure_diseq_elim                       true
% 47.95/6.49  --brand_transform                       false
% 47.95/6.49  --non_eq_to_eq                          false
% 47.95/6.49  --prep_def_merge                        true
% 47.95/6.49  --prep_def_merge_prop_impl              false
% 47.95/6.49  --prep_def_merge_mbd                    true
% 47.95/6.49  --prep_def_merge_tr_red                 false
% 47.95/6.49  --prep_def_merge_tr_cl                  false
% 47.95/6.49  --smt_preprocessing                     true
% 47.95/6.49  --smt_ac_axioms                         fast
% 47.95/6.49  --preprocessed_out                      false
% 47.95/6.49  --preprocessed_stats                    false
% 47.95/6.49  
% 47.95/6.49  ------ Abstraction refinement Options
% 47.95/6.49  
% 47.95/6.49  --abstr_ref                             []
% 47.95/6.49  --abstr_ref_prep                        false
% 47.95/6.49  --abstr_ref_until_sat                   false
% 47.95/6.49  --abstr_ref_sig_restrict                funpre
% 47.95/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.95/6.49  --abstr_ref_under                       []
% 47.95/6.49  
% 47.95/6.49  ------ SAT Options
% 47.95/6.49  
% 47.95/6.49  --sat_mode                              false
% 47.95/6.49  --sat_fm_restart_options                ""
% 47.95/6.49  --sat_gr_def                            false
% 47.95/6.49  --sat_epr_types                         true
% 47.95/6.49  --sat_non_cyclic_types                  false
% 47.95/6.49  --sat_finite_models                     false
% 47.95/6.49  --sat_fm_lemmas                         false
% 47.95/6.49  --sat_fm_prep                           false
% 47.95/6.49  --sat_fm_uc_incr                        true
% 47.95/6.49  --sat_out_model                         small
% 47.95/6.49  --sat_out_clauses                       false
% 47.95/6.49  
% 47.95/6.49  ------ QBF Options
% 47.95/6.49  
% 47.95/6.49  --qbf_mode                              false
% 47.95/6.49  --qbf_elim_univ                         false
% 47.95/6.49  --qbf_dom_inst                          none
% 47.95/6.49  --qbf_dom_pre_inst                      false
% 47.95/6.49  --qbf_sk_in                             false
% 47.95/6.49  --qbf_pred_elim                         true
% 47.95/6.49  --qbf_split                             512
% 47.95/6.49  
% 47.95/6.49  ------ BMC1 Options
% 47.95/6.49  
% 47.95/6.49  --bmc1_incremental                      false
% 47.95/6.49  --bmc1_axioms                           reachable_all
% 47.95/6.49  --bmc1_min_bound                        0
% 47.95/6.49  --bmc1_max_bound                        -1
% 47.95/6.49  --bmc1_max_bound_default                -1
% 47.95/6.49  --bmc1_symbol_reachability              true
% 47.95/6.49  --bmc1_property_lemmas                  false
% 47.95/6.49  --bmc1_k_induction                      false
% 47.95/6.49  --bmc1_non_equiv_states                 false
% 47.95/6.49  --bmc1_deadlock                         false
% 47.95/6.49  --bmc1_ucm                              false
% 47.95/6.49  --bmc1_add_unsat_core                   none
% 47.95/6.49  --bmc1_unsat_core_children              false
% 47.95/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.95/6.49  --bmc1_out_stat                         full
% 47.95/6.49  --bmc1_ground_init                      false
% 47.95/6.49  --bmc1_pre_inst_next_state              false
% 47.95/6.49  --bmc1_pre_inst_state                   false
% 47.95/6.49  --bmc1_pre_inst_reach_state             false
% 47.95/6.49  --bmc1_out_unsat_core                   false
% 47.95/6.49  --bmc1_aig_witness_out                  false
% 47.95/6.49  --bmc1_verbose                          false
% 47.95/6.49  --bmc1_dump_clauses_tptp                false
% 47.95/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.95/6.49  --bmc1_dump_file                        -
% 47.95/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.95/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.95/6.49  --bmc1_ucm_extend_mode                  1
% 47.95/6.49  --bmc1_ucm_init_mode                    2
% 47.95/6.49  --bmc1_ucm_cone_mode                    none
% 47.95/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.95/6.49  --bmc1_ucm_relax_model                  4
% 47.95/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.95/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.95/6.49  --bmc1_ucm_layered_model                none
% 47.95/6.49  --bmc1_ucm_max_lemma_size               10
% 47.95/6.49  
% 47.95/6.49  ------ AIG Options
% 47.95/6.49  
% 47.95/6.49  --aig_mode                              false
% 47.95/6.49  
% 47.95/6.49  ------ Instantiation Options
% 47.95/6.49  
% 47.95/6.49  --instantiation_flag                    true
% 47.95/6.49  --inst_sos_flag                         false
% 47.95/6.49  --inst_sos_phase                        true
% 47.95/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.95/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.95/6.49  --inst_lit_sel_side                     num_symb
% 47.95/6.49  --inst_solver_per_active                1400
% 47.95/6.49  --inst_solver_calls_frac                1.
% 47.95/6.49  --inst_passive_queue_type               priority_queues
% 47.95/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.95/6.49  --inst_passive_queues_freq              [25;2]
% 47.95/6.49  --inst_dismatching                      true
% 47.95/6.49  --inst_eager_unprocessed_to_passive     true
% 47.95/6.49  --inst_prop_sim_given                   true
% 47.95/6.49  --inst_prop_sim_new                     false
% 47.95/6.49  --inst_subs_new                         false
% 47.95/6.49  --inst_eq_res_simp                      false
% 47.95/6.49  --inst_subs_given                       false
% 47.95/6.49  --inst_orphan_elimination               true
% 47.95/6.49  --inst_learning_loop_flag               true
% 47.95/6.49  --inst_learning_start                   3000
% 47.95/6.49  --inst_learning_factor                  2
% 47.95/6.49  --inst_start_prop_sim_after_learn       3
% 47.95/6.49  --inst_sel_renew                        solver
% 47.95/6.49  --inst_lit_activity_flag                true
% 47.95/6.49  --inst_restr_to_given                   false
% 47.95/6.49  --inst_activity_threshold               500
% 47.95/6.49  --inst_out_proof                        true
% 47.95/6.49  
% 47.95/6.49  ------ Resolution Options
% 47.95/6.49  
% 47.95/6.49  --resolution_flag                       true
% 47.95/6.49  --res_lit_sel                           adaptive
% 47.95/6.49  --res_lit_sel_side                      none
% 47.95/6.49  --res_ordering                          kbo
% 47.95/6.49  --res_to_prop_solver                    active
% 47.95/6.49  --res_prop_simpl_new                    false
% 47.95/6.49  --res_prop_simpl_given                  true
% 47.95/6.49  --res_passive_queue_type                priority_queues
% 47.95/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.95/6.49  --res_passive_queues_freq               [15;5]
% 47.95/6.49  --res_forward_subs                      full
% 47.95/6.49  --res_backward_subs                     full
% 47.95/6.49  --res_forward_subs_resolution           true
% 47.95/6.49  --res_backward_subs_resolution          true
% 47.95/6.49  --res_orphan_elimination                true
% 47.95/6.49  --res_time_limit                        2.
% 47.95/6.49  --res_out_proof                         true
% 47.95/6.49  
% 47.95/6.49  ------ Superposition Options
% 47.95/6.49  
% 47.95/6.49  --superposition_flag                    true
% 47.95/6.49  --sup_passive_queue_type                priority_queues
% 47.95/6.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.95/6.49  --sup_passive_queues_freq               [1;4]
% 47.95/6.49  --demod_completeness_check              fast
% 47.95/6.49  --demod_use_ground                      true
% 47.95/6.49  --sup_to_prop_solver                    passive
% 47.95/6.49  --sup_prop_simpl_new                    true
% 47.95/6.49  --sup_prop_simpl_given                  true
% 47.95/6.49  --sup_fun_splitting                     false
% 47.95/6.49  --sup_smt_interval                      50000
% 47.95/6.49  
% 47.95/6.49  ------ Superposition Simplification Setup
% 47.95/6.49  
% 47.95/6.49  --sup_indices_passive                   []
% 47.95/6.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.95/6.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.95/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.95/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.95/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.95/6.49  --sup_full_bw                           [BwDemod]
% 47.95/6.49  --sup_immed_triv                        [TrivRules]
% 47.95/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.95/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.95/6.49  --sup_immed_bw_main                     []
% 47.95/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.95/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.95/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.95/6.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.95/6.49  
% 47.95/6.49  ------ Combination Options
% 47.95/6.49  
% 47.95/6.49  --comb_res_mult                         3
% 47.95/6.49  --comb_sup_mult                         2
% 47.95/6.49  --comb_inst_mult                        10
% 47.95/6.49  
% 47.95/6.49  ------ Debug Options
% 47.95/6.49  
% 47.95/6.49  --dbg_backtrace                         false
% 47.95/6.49  --dbg_dump_prop_clauses                 false
% 47.95/6.49  --dbg_dump_prop_clauses_file            -
% 47.95/6.49  --dbg_out_stat                          false
% 47.95/6.49  
% 47.95/6.49  
% 47.95/6.49  
% 47.95/6.49  
% 47.95/6.49  ------ Proving...
% 47.95/6.49  
% 47.95/6.49  
% 47.95/6.49  % SZS status Theorem for theBenchmark.p
% 47.95/6.49  
% 47.95/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.95/6.49  
% 47.95/6.49  fof(f2,axiom,(
% 47.95/6.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f28,plain,(
% 47.95/6.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 47.95/6.49    inference(nnf_transformation,[],[f2])).
% 47.95/6.49  
% 47.95/6.49  fof(f29,plain,(
% 47.95/6.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 47.95/6.49    inference(flattening,[],[f28])).
% 47.95/6.49  
% 47.95/6.49  fof(f30,plain,(
% 47.95/6.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 47.95/6.49    inference(rectify,[],[f29])).
% 47.95/6.49  
% 47.95/6.49  fof(f31,plain,(
% 47.95/6.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 47.95/6.49    introduced(choice_axiom,[])).
% 47.95/6.49  
% 47.95/6.49  fof(f32,plain,(
% 47.95/6.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 47.95/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 47.95/6.49  
% 47.95/6.49  fof(f47,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f32])).
% 47.95/6.49  
% 47.95/6.49  fof(f4,axiom,(
% 47.95/6.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f51,plain,(
% 47.95/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 47.95/6.49    inference(cnf_transformation,[],[f4])).
% 47.95/6.49  
% 47.95/6.49  fof(f6,axiom,(
% 47.95/6.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f53,plain,(
% 47.95/6.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 47.95/6.49    inference(cnf_transformation,[],[f6])).
% 47.95/6.49  
% 47.95/6.49  fof(f64,plain,(
% 47.95/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 47.95/6.49    inference(definition_unfolding,[],[f51,f53])).
% 47.95/6.49  
% 47.95/6.49  fof(f73,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 47.95/6.49    inference(definition_unfolding,[],[f47,f64])).
% 47.95/6.49  
% 47.95/6.49  fof(f48,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f32])).
% 47.95/6.49  
% 47.95/6.49  fof(f72,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 47.95/6.49    inference(definition_unfolding,[],[f48,f64])).
% 47.95/6.49  
% 47.95/6.49  fof(f3,axiom,(
% 47.95/6.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f13,plain,(
% 47.95/6.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 47.95/6.49    inference(rectify,[],[f3])).
% 47.95/6.49  
% 47.95/6.49  fof(f50,plain,(
% 47.95/6.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 47.95/6.49    inference(cnf_transformation,[],[f13])).
% 47.95/6.49  
% 47.95/6.49  fof(f77,plain,(
% 47.95/6.49    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 47.95/6.49    inference(definition_unfolding,[],[f50,f53])).
% 47.95/6.49  
% 47.95/6.49  fof(f11,conjecture,(
% 47.95/6.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f12,negated_conjecture,(
% 47.95/6.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 47.95/6.49    inference(negated_conjecture,[],[f11])).
% 47.95/6.49  
% 47.95/6.49  fof(f21,plain,(
% 47.95/6.49    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 47.95/6.49    inference(ennf_transformation,[],[f12])).
% 47.95/6.49  
% 47.95/6.49  fof(f22,plain,(
% 47.95/6.49    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 47.95/6.49    inference(flattening,[],[f21])).
% 47.95/6.49  
% 47.95/6.49  fof(f33,plain,(
% 47.95/6.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 47.95/6.49    inference(nnf_transformation,[],[f22])).
% 47.95/6.49  
% 47.95/6.49  fof(f34,plain,(
% 47.95/6.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 47.95/6.49    inference(flattening,[],[f33])).
% 47.95/6.49  
% 47.95/6.49  fof(f36,plain,(
% 47.95/6.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK3),sK3) != k2_tops_1(X0,sK3) | ~v3_pre_topc(sK3,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK3),sK3) = k2_tops_1(X0,sK3) | v3_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.95/6.49    introduced(choice_axiom,[])).
% 47.95/6.49  
% 47.95/6.49  fof(f35,plain,(
% 47.95/6.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X1),X1) != k2_tops_1(sK2,X1) | ~v3_pre_topc(X1,sK2)) & (k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,X1),X1) = k2_tops_1(sK2,X1) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 47.95/6.49    introduced(choice_axiom,[])).
% 47.95/6.49  
% 47.95/6.49  fof(f37,plain,(
% 47.95/6.49    ((k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)) & (k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 47.95/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).
% 47.95/6.49  
% 47.95/6.49  fof(f62,plain,(
% 47.95/6.49    k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) | v3_pre_topc(sK3,sK2)),
% 47.95/6.49    inference(cnf_transformation,[],[f37])).
% 47.95/6.49  
% 47.95/6.49  fof(f61,plain,(
% 47.95/6.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 47.95/6.49    inference(cnf_transformation,[],[f37])).
% 47.95/6.49  
% 47.95/6.49  fof(f9,axiom,(
% 47.95/6.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f18,plain,(
% 47.95/6.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 47.95/6.49    inference(ennf_transformation,[],[f9])).
% 47.95/6.49  
% 47.95/6.49  fof(f19,plain,(
% 47.95/6.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 47.95/6.49    inference(flattening,[],[f18])).
% 47.95/6.49  
% 47.95/6.49  fof(f56,plain,(
% 47.95/6.49    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f19])).
% 47.95/6.49  
% 47.95/6.49  fof(f59,plain,(
% 47.95/6.49    v2_pre_topc(sK2)),
% 47.95/6.49    inference(cnf_transformation,[],[f37])).
% 47.95/6.49  
% 47.95/6.49  fof(f60,plain,(
% 47.95/6.49    l1_pre_topc(sK2)),
% 47.95/6.49    inference(cnf_transformation,[],[f37])).
% 47.95/6.49  
% 47.95/6.49  fof(f7,axiom,(
% 47.95/6.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f15,plain,(
% 47.95/6.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 47.95/6.49    inference(ennf_transformation,[],[f7])).
% 47.95/6.49  
% 47.95/6.49  fof(f16,plain,(
% 47.95/6.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 47.95/6.49    inference(flattening,[],[f15])).
% 47.95/6.49  
% 47.95/6.49  fof(f54,plain,(
% 47.95/6.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f16])).
% 47.95/6.49  
% 47.95/6.49  fof(f5,axiom,(
% 47.95/6.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f14,plain,(
% 47.95/6.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.95/6.49    inference(ennf_transformation,[],[f5])).
% 47.95/6.49  
% 47.95/6.49  fof(f52,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.95/6.49    inference(cnf_transformation,[],[f14])).
% 47.95/6.49  
% 47.95/6.49  fof(f78,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.95/6.49    inference(definition_unfolding,[],[f52,f64])).
% 47.95/6.49  
% 47.95/6.49  fof(f45,plain,(
% 47.95/6.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 47.95/6.49    inference(cnf_transformation,[],[f32])).
% 47.95/6.49  
% 47.95/6.49  fof(f75,plain,(
% 47.95/6.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 47.95/6.49    inference(definition_unfolding,[],[f45,f64])).
% 47.95/6.49  
% 47.95/6.49  fof(f83,plain,(
% 47.95/6.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 47.95/6.49    inference(equality_resolution,[],[f75])).
% 47.95/6.49  
% 47.95/6.49  fof(f57,plain,(
% 47.95/6.49    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f19])).
% 47.95/6.49  
% 47.95/6.49  fof(f10,axiom,(
% 47.95/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f20,plain,(
% 47.95/6.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.95/6.49    inference(ennf_transformation,[],[f10])).
% 47.95/6.49  
% 47.95/6.49  fof(f58,plain,(
% 47.95/6.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f20])).
% 47.95/6.49  
% 47.95/6.49  fof(f1,axiom,(
% 47.95/6.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f23,plain,(
% 47.95/6.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 47.95/6.49    inference(nnf_transformation,[],[f1])).
% 47.95/6.49  
% 47.95/6.49  fof(f24,plain,(
% 47.95/6.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 47.95/6.49    inference(flattening,[],[f23])).
% 47.95/6.49  
% 47.95/6.49  fof(f25,plain,(
% 47.95/6.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 47.95/6.49    inference(rectify,[],[f24])).
% 47.95/6.49  
% 47.95/6.49  fof(f26,plain,(
% 47.95/6.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 47.95/6.49    introduced(choice_axiom,[])).
% 47.95/6.49  
% 47.95/6.49  fof(f27,plain,(
% 47.95/6.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 47.95/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 47.95/6.49  
% 47.95/6.49  fof(f42,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f27])).
% 47.95/6.49  
% 47.95/6.49  fof(f66,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 47.95/6.49    inference(definition_unfolding,[],[f42,f53])).
% 47.95/6.49  
% 47.95/6.49  fof(f44,plain,(
% 47.95/6.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 47.95/6.49    inference(cnf_transformation,[],[f32])).
% 47.95/6.49  
% 47.95/6.49  fof(f76,plain,(
% 47.95/6.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 47.95/6.49    inference(definition_unfolding,[],[f44,f64])).
% 47.95/6.49  
% 47.95/6.49  fof(f84,plain,(
% 47.95/6.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 47.95/6.49    inference(equality_resolution,[],[f76])).
% 47.95/6.49  
% 47.95/6.49  fof(f43,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f27])).
% 47.95/6.49  
% 47.95/6.49  fof(f65,plain,(
% 47.95/6.49    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 47.95/6.49    inference(definition_unfolding,[],[f43,f53])).
% 47.95/6.49  
% 47.95/6.49  fof(f46,plain,(
% 47.95/6.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 47.95/6.49    inference(cnf_transformation,[],[f32])).
% 47.95/6.49  
% 47.95/6.49  fof(f74,plain,(
% 47.95/6.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 47.95/6.49    inference(definition_unfolding,[],[f46,f64])).
% 47.95/6.49  
% 47.95/6.49  fof(f82,plain,(
% 47.95/6.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 47.95/6.49    inference(equality_resolution,[],[f74])).
% 47.95/6.49  
% 47.95/6.49  fof(f8,axiom,(
% 47.95/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 47.95/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.95/6.49  
% 47.95/6.49  fof(f17,plain,(
% 47.95/6.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.95/6.49    inference(ennf_transformation,[],[f8])).
% 47.95/6.49  
% 47.95/6.49  fof(f55,plain,(
% 47.95/6.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.95/6.49    inference(cnf_transformation,[],[f17])).
% 47.95/6.49  
% 47.95/6.49  fof(f63,plain,(
% 47.95/6.49    k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)),
% 47.95/6.49    inference(cnf_transformation,[],[f37])).
% 47.95/6.49  
% 47.95/6.49  cnf(c_8,plain,
% 47.95/6.49      ( r2_hidden(sK1(X0,X1,X2),X0)
% 47.95/6.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 47.95/6.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ),
% 47.95/6.49      inference(cnf_transformation,[],[f73]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_897,plain,
% 47.95/6.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
% 47.95/6.49      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 47.95/6.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_7,plain,
% 47.95/6.49      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 47.95/6.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 47.95/6.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ),
% 47.95/6.49      inference(cnf_transformation,[],[f72]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_898,plain,
% 47.95/6.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
% 47.95/6.49      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 47.95/6.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_2727,plain,
% 47.95/6.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1
% 47.95/6.49      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_897,c_898]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_12,plain,
% 47.95/6.49      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 47.95/6.49      inference(cnf_transformation,[],[f77]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_2743,plain,
% 47.95/6.49      ( k5_xboole_0(X0,X0) = X1
% 47.95/6.49      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 47.95/6.49      inference(light_normalisation,[status(thm)],[c_2727,c_12]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_20,negated_conjecture,
% 47.95/6.49      ( v3_pre_topc(sK3,sK2)
% 47.95/6.49      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
% 47.95/6.49      inference(cnf_transformation,[],[f62]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_882,plain,
% 47.95/6.49      ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
% 47.95/6.49      | v3_pre_topc(sK3,sK2) = iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_21,negated_conjecture,
% 47.95/6.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 47.95/6.49      inference(cnf_transformation,[],[f61]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_881,plain,
% 47.95/6.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_17,plain,
% 47.95/6.49      ( ~ v3_pre_topc(X0,X1)
% 47.95/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 47.95/6.49      | ~ v2_pre_topc(X3)
% 47.95/6.49      | ~ l1_pre_topc(X3)
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | k1_tops_1(X1,X0) = X0 ),
% 47.95/6.49      inference(cnf_transformation,[],[f56]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_261,plain,
% 47.95/6.49      ( ~ v3_pre_topc(X0,X1)
% 47.95/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | k1_tops_1(X1,X0) = X0
% 47.95/6.49      | ~ sP1_iProver_split ),
% 47.95/6.49      inference(splitting,
% 47.95/6.49                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 47.95/6.49                [c_17]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_886,plain,
% 47.95/6.49      ( k1_tops_1(X0,X1) = X1
% 47.95/6.49      | v3_pre_topc(X1,X0) != iProver_top
% 47.95/6.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 47.95/6.49      | l1_pre_topc(X0) != iProver_top
% 47.95/6.49      | sP1_iProver_split != iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_1706,plain,
% 47.95/6.49      ( k1_tops_1(sK2,sK3) = sK3
% 47.95/6.49      | v3_pre_topc(sK3,sK2) != iProver_top
% 47.95/6.49      | l1_pre_topc(sK2) != iProver_top
% 47.95/6.49      | sP1_iProver_split != iProver_top ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_881,c_886]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_23,negated_conjecture,
% 47.95/6.49      ( v2_pre_topc(sK2) ),
% 47.95/6.49      inference(cnf_transformation,[],[f59]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_24,plain,
% 47.95/6.49      ( v2_pre_topc(sK2) = iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_22,negated_conjecture,
% 47.95/6.49      ( l1_pre_topc(sK2) ),
% 47.95/6.49      inference(cnf_transformation,[],[f60]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_25,plain,
% 47.95/6.49      ( l1_pre_topc(sK2) = iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_262,plain,
% 47.95/6.49      ( sP1_iProver_split | sP0_iProver_split ),
% 47.95/6.49      inference(splitting,
% 47.95/6.49                [splitting(split),new_symbols(definition,[])],
% 47.95/6.49                [c_17]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_301,plain,
% 47.95/6.49      ( sP1_iProver_split = iProver_top
% 47.95/6.49      | sP0_iProver_split = iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_260,plain,
% 47.95/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ v2_pre_topc(X1)
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | ~ sP0_iProver_split ),
% 47.95/6.49      inference(splitting,
% 47.95/6.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 47.95/6.49                [c_17]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_887,plain,
% 47.95/6.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 47.95/6.49      | v2_pre_topc(X1) != iProver_top
% 47.95/6.49      | l1_pre_topc(X1) != iProver_top
% 47.95/6.49      | sP0_iProver_split != iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_2182,plain,
% 47.95/6.49      ( v2_pre_topc(sK2) != iProver_top
% 47.95/6.49      | l1_pre_topc(sK2) != iProver_top
% 47.95/6.49      | sP0_iProver_split != iProver_top ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_881,c_887]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_3749,plain,
% 47.95/6.49      ( k1_tops_1(sK2,sK3) = sK3 | v3_pre_topc(sK3,sK2) != iProver_top ),
% 47.95/6.49      inference(global_propositional_subsumption,
% 47.95/6.49                [status(thm)],
% 47.95/6.49                [c_1706,c_24,c_25,c_301,c_2182]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_3755,plain,
% 47.95/6.49      ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3)
% 47.95/6.49      | k1_tops_1(sK2,sK3) = sK3 ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_882,c_3749]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_14,plain,
% 47.95/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ l1_pre_topc(X1) ),
% 47.95/6.49      inference(cnf_transformation,[],[f54]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_892,plain,
% 47.95/6.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 47.95/6.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 47.95/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_13,plain,
% 47.95/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.95/6.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 47.95/6.49      inference(cnf_transformation,[],[f78]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_893,plain,
% 47.95/6.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 47.95/6.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_1805,plain,
% 47.95/6.49      ( k5_xboole_0(k2_pre_topc(X0,X1),k1_setfam_1(k2_tarski(k2_pre_topc(X0,X1),X2))) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2)
% 47.95/6.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 47.95/6.49      | l1_pre_topc(X0) != iProver_top ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_892,c_893]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_5008,plain,
% 47.95/6.49      ( k5_xboole_0(k2_pre_topc(sK2,sK3),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,sK3),X0))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0)
% 47.95/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_881,c_1805]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_1142,plain,
% 47.95/6.49      ( m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 47.95/6.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 47.95/6.49      | ~ l1_pre_topc(sK2) ),
% 47.95/6.49      inference(instantiation,[status(thm)],[c_14]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_1263,plain,
% 47.95/6.49      ( ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 47.95/6.49      | k5_xboole_0(k2_pre_topc(sK2,sK3),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,sK3),X0))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0) ),
% 47.95/6.49      inference(instantiation,[status(thm)],[c_13]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_8628,plain,
% 47.95/6.49      ( k5_xboole_0(k2_pre_topc(sK2,sK3),k1_setfam_1(k2_tarski(k2_pre_topc(sK2,sK3),X0))) = k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X0) ),
% 47.95/6.49      inference(global_propositional_subsumption,
% 47.95/6.49                [status(thm)],
% 47.95/6.49                [c_5008,c_22,c_21,c_1142,c_1263]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_10,plain,
% 47.95/6.49      ( ~ r2_hidden(X0,X1)
% 47.95/6.49      | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
% 47.95/6.49      inference(cnf_transformation,[],[f83]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_895,plain,
% 47.95/6.49      ( r2_hidden(X0,X1) != iProver_top
% 47.95/6.49      | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) != iProver_top ),
% 47.95/6.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_8638,plain,
% 47.95/6.49      ( r2_hidden(X0,X1) != iProver_top
% 47.95/6.49      | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),X1)) != iProver_top ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_8628,c_895]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_8957,plain,
% 47.95/6.49      ( k1_tops_1(sK2,sK3) = sK3
% 47.95/6.49      | r2_hidden(X0,k2_tops_1(sK2,sK3)) != iProver_top
% 47.95/6.49      | r2_hidden(X0,sK3) != iProver_top ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_3755,c_8638]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_145359,plain,
% 47.95/6.49      ( k1_tops_1(sK2,sK3) = sK3
% 47.95/6.49      | k5_xboole_0(X0,X0) = k2_tops_1(sK2,sK3)
% 47.95/6.49      | r2_hidden(sK1(X0,X0,k2_tops_1(sK2,sK3)),sK3) != iProver_top ),
% 47.95/6.49      inference(superposition,[status(thm)],[c_2743,c_8957]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_1707,plain,
% 47.95/6.49      ( ~ v3_pre_topc(sK3,sK2)
% 47.95/6.49      | ~ l1_pre_topc(sK2)
% 47.95/6.49      | ~ sP1_iProver_split
% 47.95/6.49      | k1_tops_1(sK2,sK3) = sK3 ),
% 47.95/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_1706]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_2189,plain,
% 47.95/6.49      ( ~ v2_pre_topc(sK2) | ~ l1_pre_topc(sK2) | ~ sP0_iProver_split ),
% 47.95/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_2182]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_274,plain,
% 47.95/6.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.95/6.49      theory(equality) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_267,plain,( X0 = X0 ),theory(equality) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_3797,plain,
% 47.95/6.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 47.95/6.49      inference(resolution,[status(thm)],[c_274,c_267]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_273,plain,
% 47.95/6.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 47.95/6.49      theory(equality) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_13487,plain,
% 47.95/6.49      ( ~ m1_subset_1(k1_zfmisc_1(X0),X1)
% 47.95/6.49      | m1_subset_1(k1_zfmisc_1(X2),X1)
% 47.95/6.49      | X2 != X0 ),
% 47.95/6.49      inference(resolution,[status(thm)],[c_3797,c_273]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_142731,plain,
% 47.95/6.49      ( v3_pre_topc(sK3,sK2)
% 47.95/6.49      | m1_subset_1(k1_zfmisc_1(k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3)),X0)
% 47.95/6.49      | ~ m1_subset_1(k1_zfmisc_1(k2_tops_1(sK2,sK3)),X0) ),
% 47.95/6.49      inference(resolution,[status(thm)],[c_13487,c_20]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_16,plain,
% 47.95/6.49      ( v3_pre_topc(X0,X1)
% 47.95/6.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 47.95/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ v2_pre_topc(X1)
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | ~ l1_pre_topc(X3)
% 47.95/6.49      | k1_tops_1(X1,X0) != X0 ),
% 47.95/6.49      inference(cnf_transformation,[],[f57]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_264,plain,
% 47.95/6.49      ( v3_pre_topc(X0,X1)
% 47.95/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ v2_pre_topc(X1)
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | k1_tops_1(X1,X0) != X0
% 47.95/6.49      | ~ sP3_iProver_split ),
% 47.95/6.49      inference(splitting,
% 47.95/6.49                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 47.95/6.49                [c_16]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_265,plain,
% 47.95/6.49      ( sP3_iProver_split | sP2_iProver_split ),
% 47.95/6.49      inference(splitting,
% 47.95/6.49                [splitting(split),new_symbols(definition,[])],
% 47.95/6.49                [c_16]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_263,plain,
% 47.95/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | ~ sP2_iProver_split ),
% 47.95/6.49      inference(splitting,
% 47.95/6.49                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 47.95/6.49                [c_16]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_543,plain,
% 47.95/6.49      ( k1_tops_1(X1,X0) != X0
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | ~ v2_pre_topc(X1)
% 47.95/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | v3_pre_topc(X0,X1) ),
% 47.95/6.49      inference(global_propositional_subsumption,
% 47.95/6.49                [status(thm)],
% 47.95/6.49                [c_264,c_265,c_263]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_544,plain,
% 47.95/6.49      ( v3_pre_topc(X0,X1)
% 47.95/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ v2_pre_topc(X1)
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | k1_tops_1(X1,X0) != X0 ),
% 47.95/6.49      inference(renaming,[status(thm)],[c_543]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_1187,plain,
% 47.95/6.49      ( v3_pre_topc(sK3,sK2)
% 47.95/6.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 47.95/6.49      | ~ v2_pre_topc(sK2)
% 47.95/6.49      | ~ l1_pre_topc(sK2)
% 47.95/6.49      | k1_tops_1(sK2,sK3) != sK3 ),
% 47.95/6.49      inference(instantiation,[status(thm)],[c_544]) ).
% 47.95/6.49  
% 47.95/6.49  cnf(c_18,plain,
% 47.95/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.49      | ~ l1_pre_topc(X1)
% 47.95/6.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 47.95/6.50      inference(cnf_transformation,[],[f58]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_884,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 47.95/6.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 47.95/6.50      | l1_pre_topc(X0) != iProver_top ),
% 47.95/6.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_2290,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3)
% 47.95/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_881,c_884]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_1184,plain,
% 47.95/6.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 47.95/6.50      | ~ l1_pre_topc(sK2)
% 47.95/6.50      | k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
% 47.95/6.50      inference(instantiation,[status(thm)],[c_18]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_4326,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
% 47.95/6.50      inference(global_propositional_subsumption,
% 47.95/6.50                [status(thm)],
% 47.95/6.50                [c_2290,c_22,c_21,c_1184]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_1,plain,
% 47.95/6.50      ( r2_hidden(sK0(X0,X1,X2),X1)
% 47.95/6.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 47.95/6.50      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 47.95/6.50      inference(cnf_transformation,[],[f66]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_904,plain,
% 47.95/6.50      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 47.95/6.50      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 47.95/6.50      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 47.95/6.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_1582,plain,
% 47.95/6.50      ( k5_xboole_0(sK3,k1_setfam_1(k2_tarski(sK3,X0))) = k7_subset_1(u1_struct_0(sK2),sK3,X0) ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_881,c_893]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_11,plain,
% 47.95/6.50      ( r2_hidden(X0,X1)
% 47.95/6.50      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
% 47.95/6.50      inference(cnf_transformation,[],[f84]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_894,plain,
% 47.95/6.50      ( r2_hidden(X0,X1) = iProver_top
% 47.95/6.50      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) != iProver_top ),
% 47.95/6.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_3646,plain,
% 47.95/6.50      ( r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),sK3,X1)) != iProver_top
% 47.95/6.50      | r2_hidden(X0,sK3) = iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_1582,c_894]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_3929,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(X1,X2))
% 47.95/6.50      | r2_hidden(sK0(X1,X2,k7_subset_1(u1_struct_0(sK2),sK3,X0)),X2) = iProver_top
% 47.95/6.50      | r2_hidden(sK0(X1,X2,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_904,c_3646]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_8847,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(X1,sK3))
% 47.95/6.50      | r2_hidden(sK0(X1,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top
% 47.95/6.50      | iProver_top != iProver_top ),
% 47.95/6.50      inference(equality_factoring,[status(thm)],[c_3929]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_8849,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(X1,sK3))
% 47.95/6.50      | r2_hidden(sK0(X1,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top ),
% 47.95/6.50      inference(equality_resolution_simp,[status(thm)],[c_8847]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_0,plain,
% 47.95/6.50      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 47.95/6.50      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 47.95/6.50      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 47.95/6.50      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 47.95/6.50      inference(cnf_transformation,[],[f65]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_905,plain,
% 47.95/6.50      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 47.95/6.50      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 47.95/6.50      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 47.95/6.50      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 47.95/6.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_115476,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(sK3,sK3))
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),k7_subset_1(u1_struct_0(sK2),sK3,X0)) != iProver_top
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) != iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_8849,c_905]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_115495,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(sK3,sK3))
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),k7_subset_1(u1_struct_0(sK2),sK3,X0)) != iProver_top ),
% 47.95/6.50      inference(forward_subsumption_resolution,
% 47.95/6.50                [status(thm)],
% 47.95/6.50                [c_115476,c_8849]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_115496,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),k7_subset_1(u1_struct_0(sK2),sK3,X0)) != iProver_top ),
% 47.95/6.50      inference(demodulation,[status(thm)],[c_115495,c_12]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_116226,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_setfam_1(k2_tarski(sK3,sK3))
% 47.95/6.50      | k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_904,c_115496]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_116255,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) = iProver_top ),
% 47.95/6.50      inference(demodulation,[status(thm)],[c_116226,c_12]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_116877,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) = iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_4326,c_116255]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_116895,plain,
% 47.95/6.50      ( k1_tops_1(sK2,sK3) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) = iProver_top ),
% 47.95/6.50      inference(demodulation,[status(thm)],[c_116877,c_4326]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_9,plain,
% 47.95/6.50      ( ~ r2_hidden(X0,X1)
% 47.95/6.50      | r2_hidden(X0,X2)
% 47.95/6.50      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
% 47.95/6.50      inference(cnf_transformation,[],[f82]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_896,plain,
% 47.95/6.50      ( r2_hidden(X0,X1) != iProver_top
% 47.95/6.50      | r2_hidden(X0,X2) = iProver_top
% 47.95/6.50      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = iProver_top ),
% 47.95/6.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_3645,plain,
% 47.95/6.50      ( r2_hidden(X0,X1) = iProver_top
% 47.95/6.50      | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),sK3,X1)) = iProver_top
% 47.95/6.50      | r2_hidden(X0,sK3) != iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_1582,c_896]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_116228,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),X0) = iProver_top
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),sK3) != iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_3645,c_115496]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_116258,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,X0)),X0) = iProver_top ),
% 47.95/6.50      inference(backward_subsumption_resolution,
% 47.95/6.50                [status(thm)],
% 47.95/6.50                [c_116255,c_116228]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_145447,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = sK3
% 47.95/6.50      | k1_tops_1(sK2,sK3) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3))),sK3) != iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_116258,c_8957]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_145486,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = sK3
% 47.95/6.50      | k1_tops_1(sK2,sK3) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) != iProver_top ),
% 47.95/6.50      inference(light_normalisation,[status(thm)],[c_145447,c_4326]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_145487,plain,
% 47.95/6.50      ( k1_tops_1(sK2,sK3) = sK3
% 47.95/6.50      | r2_hidden(sK0(sK3,sK3,k1_tops_1(sK2,sK3)),sK3) != iProver_top ),
% 47.95/6.50      inference(demodulation,[status(thm)],[c_145486,c_4326]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_146890,plain,
% 47.95/6.50      ( v3_pre_topc(sK3,sK2) ),
% 47.95/6.50      inference(global_propositional_subsumption,
% 47.95/6.50                [status(thm)],
% 47.95/6.50                [c_142731,c_23,c_22,c_21,c_1187,c_116895,c_145487]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_152069,plain,
% 47.95/6.50      ( k1_tops_1(sK2,sK3) = sK3 ),
% 47.95/6.50      inference(global_propositional_subsumption,
% 47.95/6.50                [status(thm)],
% 47.95/6.50                [c_145359,c_116895,c_145487]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_15,plain,
% 47.95/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.95/6.50      | ~ l1_pre_topc(X1)
% 47.95/6.50      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 47.95/6.50      inference(cnf_transformation,[],[f55]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_891,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 47.95/6.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 47.95/6.50      | l1_pre_topc(X0) != iProver_top ),
% 47.95/6.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_3017,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k1_tops_1(sK2,sK3)) = k2_tops_1(sK2,sK3)
% 47.95/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 47.95/6.50      inference(superposition,[status(thm)],[c_881,c_891]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_1190,plain,
% 47.95/6.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 47.95/6.50      | ~ l1_pre_topc(sK2)
% 47.95/6.50      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k1_tops_1(sK2,sK3)) = k2_tops_1(sK2,sK3) ),
% 47.95/6.50      inference(instantiation,[status(thm)],[c_15]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_5390,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),k1_tops_1(sK2,sK3)) = k2_tops_1(sK2,sK3) ),
% 47.95/6.50      inference(global_propositional_subsumption,
% 47.95/6.50                [status(thm)],
% 47.95/6.50                [c_3017,c_22,c_21,c_1190]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_152094,plain,
% 47.95/6.50      ( k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) = k2_tops_1(sK2,sK3) ),
% 47.95/6.50      inference(demodulation,[status(thm)],[c_152069,c_5390]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(c_19,negated_conjecture,
% 47.95/6.50      ( ~ v3_pre_topc(sK3,sK2)
% 47.95/6.50      | k7_subset_1(u1_struct_0(sK2),k2_pre_topc(sK2,sK3),sK3) != k2_tops_1(sK2,sK3) ),
% 47.95/6.50      inference(cnf_transformation,[],[f63]) ).
% 47.95/6.50  
% 47.95/6.50  cnf(contradiction,plain,
% 47.95/6.50      ( $false ),
% 47.95/6.50      inference(minisat,[status(thm)],[c_152094,c_146890,c_19]) ).
% 47.95/6.50  
% 47.95/6.50  
% 47.95/6.50  % SZS output end CNFRefutation for theBenchmark.p
% 47.95/6.50  
% 47.95/6.50  ------                               Statistics
% 47.95/6.50  
% 47.95/6.50  ------ Selected
% 47.95/6.50  
% 47.95/6.50  total_time:                             5.886
% 47.95/6.50  
%------------------------------------------------------------------------------

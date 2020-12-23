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
% DateTime   : Thu Dec  3 12:15:02 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  162 (1188 expanded)
%              Number of clauses        :  105 ( 298 expanded)
%              Number of leaves         :   17 ( 298 expanded)
%              Depth                    :   27
%              Number of atoms          :  604 (10136 expanded)
%              Number of equality atoms :  179 (1745 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK4
        & v3_pre_topc(sK4,X0)
        & r1_tarski(sK4,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
              & r1_tarski(X2,sK3)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tops_1(sK3,X0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,X0)
              | ~ r1_tarski(X3,sK3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tops_1(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
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
                & v3_pre_topc(X2,sK2)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
            | ~ v2_tops_1(X1,sK2) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK2)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            | v2_tops_1(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ( k1_xboole_0 != sK4
        & v3_pre_topc(sK4,sK2)
        & r1_tarski(sK4,sK3)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ v2_tops_1(sK3,sK2) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK2)
          | ~ r1_tarski(X3,sK3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      | v2_tops_1(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).

fof(f77,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK2)
      | ~ r1_tarski(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tops_1(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,
    ( r1_tarski(sK4,sK3)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,
    ( k1_xboole_0 != sK4
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2152,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2150,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_21,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_525,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_526,plain,
    ( ~ v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_2142,plain,
    ( k1_tops_1(sK2,X0) = k1_xboole_0
    | v2_tops_1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_3398,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2150,c_2142])).

cnf(c_13,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_410,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_411,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_28])).

cnf(c_416,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_2343,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_2361,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2394,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1552,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2467,plain,
    ( k1_tops_1(sK2,sK3) != X0
    | k1_tops_1(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_2743,plain,
    ( k1_tops_1(sK2,sK3) != k1_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_1551,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2744,plain,
    ( k1_tops_1(sK2,sK3) = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2470,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),X0)
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2748,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2470])).

cnf(c_26,negated_conjecture,
    ( v2_tops_1(sK3,sK2)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2886,plain,
    ( v2_tops_1(sK3,sK2)
    | ~ v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
    | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | k1_xboole_0 = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3045,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3415,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | k1_tops_1(sK2,sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3398])).

cnf(c_3501,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3398,c_27,c_2343,c_2361,c_2394,c_2743,c_2744,c_2748,c_2886,c_3045,c_3415])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK2,X0),k1_tops_1(sK2,X1)) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_2140,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK2,X0),k1_tops_1(sK2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_3763,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_tops_1(sK2,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3501,c_2140])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7399,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_tops_1(sK2,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3763,c_32])).

cnf(c_7409,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK4),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_7399])).

cnf(c_19,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_453,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_454,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_458,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_28])).

cnf(c_459,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_507,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(X1,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_459,c_28])).

cnf(c_508,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1548,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_508])).

cnf(c_2144,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1548])).

cnf(c_1549,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_508])).

cnf(c_1588,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1549])).

cnf(c_1589,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1548])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_428,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_429,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_433,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_28])).

cnf(c_434,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_585,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_434])).

cnf(c_586,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_1545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_586])).

cnf(c_2138,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_2757,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2150,c_2138])).

cnf(c_3670,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | k1_tops_1(sK2,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2144,c_1588,c_1589,c_2757])).

cnf(c_3671,plain,
    ( k1_tops_1(sK2,X0) = X0
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3670])).

cnf(c_3677,plain,
    ( k1_tops_1(sK2,sK4) = sK4
    | v2_tops_1(sK3,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_3671])).

cnf(c_23,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | v3_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_20,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_540,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_541,plain,
    ( v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_919,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_541])).

cnf(c_920,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_922,plain,
    ( v3_pre_topc(sK4,sK2)
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_920,c_27])).

cnf(c_924,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | v3_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_2357,plain,
    ( v2_tops_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_2358,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2357])).

cnf(c_4128,plain,
    ( k1_tops_1(sK2,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3677,c_27,c_32,c_924,c_2343,c_2358,c_2361,c_2394,c_2743,c_2744,c_2748,c_2886,c_3045,c_3415])).

cnf(c_7421,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7409,c_4128])).

cnf(c_24,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,sK3)
    | k1_tops_1(sK2,X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_541])).

cnf(c_906,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,sK3)
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_908,plain,
    ( r1_tarski(sK4,sK3)
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_906,c_27])).

cnf(c_910,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_7783,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7421,c_27,c_32,c_910,c_2343,c_2358,c_2361,c_2394,c_2743,c_2744,c_2748,c_2886,c_3045,c_3415])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2159,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7789,plain,
    ( k3_xboole_0(sK4,k1_xboole_0) = sK4 ),
    inference(superposition,[status(thm)],[c_7783,c_2159])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2158,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3228,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2158,c_2159])).

cnf(c_5,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2673,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_3123,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2673,c_6])).

cnf(c_5614,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3228,c_3123])).

cnf(c_7791,plain,
    ( sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7789,c_5614])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_541])).

cnf(c_934,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_933])).

cnf(c_936,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_934,c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7791,c_3501,c_936])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.48/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.04  
% 2.48/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/1.04  
% 2.48/1.04  ------  iProver source info
% 2.48/1.04  
% 2.48/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.48/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/1.04  git: non_committed_changes: false
% 2.48/1.04  git: last_make_outside_of_git: false
% 2.48/1.04  
% 2.48/1.04  ------ 
% 2.48/1.04  
% 2.48/1.04  ------ Input Options
% 2.48/1.04  
% 2.48/1.04  --out_options                           all
% 2.48/1.04  --tptp_safe_out                         true
% 2.48/1.04  --problem_path                          ""
% 2.48/1.04  --include_path                          ""
% 2.48/1.04  --clausifier                            res/vclausify_rel
% 2.48/1.04  --clausifier_options                    --mode clausify
% 2.48/1.04  --stdin                                 false
% 2.48/1.04  --stats_out                             all
% 2.48/1.04  
% 2.48/1.04  ------ General Options
% 2.48/1.04  
% 2.48/1.04  --fof                                   false
% 2.48/1.04  --time_out_real                         305.
% 2.48/1.04  --time_out_virtual                      -1.
% 2.48/1.04  --symbol_type_check                     false
% 2.48/1.04  --clausify_out                          false
% 2.48/1.04  --sig_cnt_out                           false
% 2.48/1.04  --trig_cnt_out                          false
% 2.48/1.04  --trig_cnt_out_tolerance                1.
% 2.48/1.04  --trig_cnt_out_sk_spl                   false
% 2.48/1.04  --abstr_cl_out                          false
% 2.48/1.04  
% 2.48/1.04  ------ Global Options
% 2.48/1.04  
% 2.48/1.04  --schedule                              default
% 2.48/1.04  --add_important_lit                     false
% 2.48/1.04  --prop_solver_per_cl                    1000
% 2.48/1.04  --min_unsat_core                        false
% 2.48/1.04  --soft_assumptions                      false
% 2.48/1.04  --soft_lemma_size                       3
% 2.48/1.04  --prop_impl_unit_size                   0
% 2.48/1.04  --prop_impl_unit                        []
% 2.48/1.04  --share_sel_clauses                     true
% 2.48/1.04  --reset_solvers                         false
% 2.48/1.04  --bc_imp_inh                            [conj_cone]
% 2.48/1.04  --conj_cone_tolerance                   3.
% 2.48/1.04  --extra_neg_conj                        none
% 2.48/1.04  --large_theory_mode                     true
% 2.48/1.04  --prolific_symb_bound                   200
% 2.48/1.04  --lt_threshold                          2000
% 2.48/1.04  --clause_weak_htbl                      true
% 2.48/1.04  --gc_record_bc_elim                     false
% 2.48/1.04  
% 2.48/1.04  ------ Preprocessing Options
% 2.48/1.04  
% 2.48/1.04  --preprocessing_flag                    true
% 2.48/1.04  --time_out_prep_mult                    0.1
% 2.48/1.04  --splitting_mode                        input
% 2.48/1.04  --splitting_grd                         true
% 2.48/1.04  --splitting_cvd                         false
% 2.48/1.04  --splitting_cvd_svl                     false
% 2.48/1.04  --splitting_nvd                         32
% 2.48/1.04  --sub_typing                            true
% 2.48/1.04  --prep_gs_sim                           true
% 2.48/1.04  --prep_unflatten                        true
% 2.48/1.04  --prep_res_sim                          true
% 2.48/1.04  --prep_upred                            true
% 2.48/1.04  --prep_sem_filter                       exhaustive
% 2.48/1.04  --prep_sem_filter_out                   false
% 2.48/1.04  --pred_elim                             true
% 2.48/1.04  --res_sim_input                         true
% 2.48/1.04  --eq_ax_congr_red                       true
% 2.48/1.04  --pure_diseq_elim                       true
% 2.48/1.04  --brand_transform                       false
% 2.48/1.04  --non_eq_to_eq                          false
% 2.48/1.04  --prep_def_merge                        true
% 2.48/1.04  --prep_def_merge_prop_impl              false
% 2.48/1.04  --prep_def_merge_mbd                    true
% 2.48/1.04  --prep_def_merge_tr_red                 false
% 2.48/1.04  --prep_def_merge_tr_cl                  false
% 2.48/1.04  --smt_preprocessing                     true
% 2.48/1.04  --smt_ac_axioms                         fast
% 2.48/1.04  --preprocessed_out                      false
% 2.48/1.04  --preprocessed_stats                    false
% 2.48/1.04  
% 2.48/1.04  ------ Abstraction refinement Options
% 2.48/1.04  
% 2.48/1.04  --abstr_ref                             []
% 2.48/1.04  --abstr_ref_prep                        false
% 2.48/1.04  --abstr_ref_until_sat                   false
% 2.48/1.04  --abstr_ref_sig_restrict                funpre
% 2.48/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.04  --abstr_ref_under                       []
% 2.48/1.04  
% 2.48/1.04  ------ SAT Options
% 2.48/1.04  
% 2.48/1.04  --sat_mode                              false
% 2.48/1.04  --sat_fm_restart_options                ""
% 2.48/1.04  --sat_gr_def                            false
% 2.48/1.04  --sat_epr_types                         true
% 2.48/1.04  --sat_non_cyclic_types                  false
% 2.48/1.04  --sat_finite_models                     false
% 2.48/1.04  --sat_fm_lemmas                         false
% 2.48/1.04  --sat_fm_prep                           false
% 2.48/1.04  --sat_fm_uc_incr                        true
% 2.48/1.04  --sat_out_model                         small
% 2.48/1.04  --sat_out_clauses                       false
% 2.48/1.04  
% 2.48/1.04  ------ QBF Options
% 2.48/1.04  
% 2.48/1.04  --qbf_mode                              false
% 2.48/1.04  --qbf_elim_univ                         false
% 2.48/1.04  --qbf_dom_inst                          none
% 2.48/1.04  --qbf_dom_pre_inst                      false
% 2.48/1.04  --qbf_sk_in                             false
% 2.48/1.04  --qbf_pred_elim                         true
% 2.48/1.04  --qbf_split                             512
% 2.48/1.04  
% 2.48/1.04  ------ BMC1 Options
% 2.48/1.04  
% 2.48/1.04  --bmc1_incremental                      false
% 2.48/1.04  --bmc1_axioms                           reachable_all
% 2.48/1.04  --bmc1_min_bound                        0
% 2.48/1.04  --bmc1_max_bound                        -1
% 2.48/1.04  --bmc1_max_bound_default                -1
% 2.48/1.04  --bmc1_symbol_reachability              true
% 2.48/1.04  --bmc1_property_lemmas                  false
% 2.48/1.04  --bmc1_k_induction                      false
% 2.48/1.04  --bmc1_non_equiv_states                 false
% 2.48/1.04  --bmc1_deadlock                         false
% 2.48/1.04  --bmc1_ucm                              false
% 2.48/1.04  --bmc1_add_unsat_core                   none
% 2.48/1.04  --bmc1_unsat_core_children              false
% 2.48/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.04  --bmc1_out_stat                         full
% 2.48/1.04  --bmc1_ground_init                      false
% 2.48/1.04  --bmc1_pre_inst_next_state              false
% 2.48/1.04  --bmc1_pre_inst_state                   false
% 2.48/1.04  --bmc1_pre_inst_reach_state             false
% 2.48/1.04  --bmc1_out_unsat_core                   false
% 2.48/1.04  --bmc1_aig_witness_out                  false
% 2.48/1.04  --bmc1_verbose                          false
% 2.48/1.04  --bmc1_dump_clauses_tptp                false
% 2.48/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.04  --bmc1_dump_file                        -
% 2.48/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.04  --bmc1_ucm_extend_mode                  1
% 2.48/1.04  --bmc1_ucm_init_mode                    2
% 2.48/1.04  --bmc1_ucm_cone_mode                    none
% 2.48/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.04  --bmc1_ucm_relax_model                  4
% 2.48/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.04  --bmc1_ucm_layered_model                none
% 2.48/1.04  --bmc1_ucm_max_lemma_size               10
% 2.48/1.04  
% 2.48/1.04  ------ AIG Options
% 2.48/1.04  
% 2.48/1.04  --aig_mode                              false
% 2.48/1.04  
% 2.48/1.04  ------ Instantiation Options
% 2.48/1.04  
% 2.48/1.04  --instantiation_flag                    true
% 2.48/1.04  --inst_sos_flag                         false
% 2.48/1.04  --inst_sos_phase                        true
% 2.48/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.04  --inst_lit_sel_side                     num_symb
% 2.48/1.04  --inst_solver_per_active                1400
% 2.48/1.04  --inst_solver_calls_frac                1.
% 2.48/1.04  --inst_passive_queue_type               priority_queues
% 2.48/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.04  --inst_passive_queues_freq              [25;2]
% 2.48/1.04  --inst_dismatching                      true
% 2.48/1.04  --inst_eager_unprocessed_to_passive     true
% 2.48/1.04  --inst_prop_sim_given                   true
% 2.48/1.04  --inst_prop_sim_new                     false
% 2.48/1.04  --inst_subs_new                         false
% 2.48/1.04  --inst_eq_res_simp                      false
% 2.48/1.04  --inst_subs_given                       false
% 2.48/1.04  --inst_orphan_elimination               true
% 2.48/1.04  --inst_learning_loop_flag               true
% 2.48/1.04  --inst_learning_start                   3000
% 2.48/1.04  --inst_learning_factor                  2
% 2.48/1.04  --inst_start_prop_sim_after_learn       3
% 2.48/1.04  --inst_sel_renew                        solver
% 2.48/1.04  --inst_lit_activity_flag                true
% 2.48/1.04  --inst_restr_to_given                   false
% 2.48/1.04  --inst_activity_threshold               500
% 2.48/1.04  --inst_out_proof                        true
% 2.48/1.04  
% 2.48/1.04  ------ Resolution Options
% 2.48/1.04  
% 2.48/1.04  --resolution_flag                       true
% 2.48/1.04  --res_lit_sel                           adaptive
% 2.48/1.04  --res_lit_sel_side                      none
% 2.48/1.04  --res_ordering                          kbo
% 2.48/1.04  --res_to_prop_solver                    active
% 2.48/1.04  --res_prop_simpl_new                    false
% 2.48/1.04  --res_prop_simpl_given                  true
% 2.48/1.04  --res_passive_queue_type                priority_queues
% 2.48/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.04  --res_passive_queues_freq               [15;5]
% 2.48/1.04  --res_forward_subs                      full
% 2.48/1.04  --res_backward_subs                     full
% 2.48/1.04  --res_forward_subs_resolution           true
% 2.48/1.04  --res_backward_subs_resolution          true
% 2.48/1.04  --res_orphan_elimination                true
% 2.48/1.04  --res_time_limit                        2.
% 2.48/1.04  --res_out_proof                         true
% 2.48/1.04  
% 2.48/1.04  ------ Superposition Options
% 2.48/1.04  
% 2.48/1.04  --superposition_flag                    true
% 2.48/1.04  --sup_passive_queue_type                priority_queues
% 2.48/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.04  --demod_completeness_check              fast
% 2.48/1.04  --demod_use_ground                      true
% 2.48/1.04  --sup_to_prop_solver                    passive
% 2.48/1.04  --sup_prop_simpl_new                    true
% 2.48/1.04  --sup_prop_simpl_given                  true
% 2.48/1.04  --sup_fun_splitting                     false
% 2.48/1.04  --sup_smt_interval                      50000
% 2.48/1.04  
% 2.48/1.04  ------ Superposition Simplification Setup
% 2.48/1.04  
% 2.48/1.04  --sup_indices_passive                   []
% 2.48/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.04  --sup_full_bw                           [BwDemod]
% 2.48/1.04  --sup_immed_triv                        [TrivRules]
% 2.48/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.04  --sup_immed_bw_main                     []
% 2.48/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.04  
% 2.48/1.04  ------ Combination Options
% 2.48/1.04  
% 2.48/1.04  --comb_res_mult                         3
% 2.48/1.04  --comb_sup_mult                         2
% 2.48/1.04  --comb_inst_mult                        10
% 2.48/1.04  
% 2.48/1.04  ------ Debug Options
% 2.48/1.04  
% 2.48/1.04  --dbg_backtrace                         false
% 2.48/1.04  --dbg_dump_prop_clauses                 false
% 2.48/1.04  --dbg_dump_prop_clauses_file            -
% 2.48/1.04  --dbg_out_stat                          false
% 2.48/1.04  ------ Parsing...
% 2.48/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/1.04  
% 2.48/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.48/1.04  
% 2.48/1.04  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/1.04  
% 2.48/1.04  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/1.04  ------ Proving...
% 2.48/1.04  ------ Problem Properties 
% 2.48/1.04  
% 2.48/1.04  
% 2.48/1.04  clauses                                 31
% 2.48/1.04  conjectures                             6
% 2.48/1.04  EPR                                     7
% 2.48/1.04  Horn                                    28
% 2.48/1.04  unary                                   7
% 2.48/1.04  binary                                  17
% 2.48/1.04  lits                                    67
% 2.48/1.04  lits eq                                 15
% 2.48/1.04  fd_pure                                 0
% 2.48/1.04  fd_pseudo                               0
% 2.48/1.04  fd_cond                                 4
% 2.48/1.04  fd_pseudo_cond                          0
% 2.48/1.04  AC symbols                              0
% 2.48/1.04  
% 2.48/1.04  ------ Schedule dynamic 5 is on 
% 2.48/1.04  
% 2.48/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/1.04  
% 2.48/1.04  
% 2.48/1.04  ------ 
% 2.48/1.04  Current options:
% 2.48/1.04  ------ 
% 2.48/1.04  
% 2.48/1.04  ------ Input Options
% 2.48/1.04  
% 2.48/1.04  --out_options                           all
% 2.48/1.04  --tptp_safe_out                         true
% 2.48/1.04  --problem_path                          ""
% 2.48/1.04  --include_path                          ""
% 2.48/1.04  --clausifier                            res/vclausify_rel
% 2.48/1.04  --clausifier_options                    --mode clausify
% 2.48/1.04  --stdin                                 false
% 2.48/1.04  --stats_out                             all
% 2.48/1.04  
% 2.48/1.04  ------ General Options
% 2.48/1.04  
% 2.48/1.04  --fof                                   false
% 2.48/1.04  --time_out_real                         305.
% 2.48/1.04  --time_out_virtual                      -1.
% 2.48/1.04  --symbol_type_check                     false
% 2.48/1.04  --clausify_out                          false
% 2.48/1.04  --sig_cnt_out                           false
% 2.48/1.04  --trig_cnt_out                          false
% 2.48/1.04  --trig_cnt_out_tolerance                1.
% 2.48/1.04  --trig_cnt_out_sk_spl                   false
% 2.48/1.04  --abstr_cl_out                          false
% 2.48/1.04  
% 2.48/1.04  ------ Global Options
% 2.48/1.04  
% 2.48/1.04  --schedule                              default
% 2.48/1.04  --add_important_lit                     false
% 2.48/1.04  --prop_solver_per_cl                    1000
% 2.48/1.04  --min_unsat_core                        false
% 2.48/1.04  --soft_assumptions                      false
% 2.48/1.04  --soft_lemma_size                       3
% 2.48/1.04  --prop_impl_unit_size                   0
% 2.48/1.04  --prop_impl_unit                        []
% 2.48/1.04  --share_sel_clauses                     true
% 2.48/1.04  --reset_solvers                         false
% 2.48/1.04  --bc_imp_inh                            [conj_cone]
% 2.48/1.04  --conj_cone_tolerance                   3.
% 2.48/1.04  --extra_neg_conj                        none
% 2.48/1.04  --large_theory_mode                     true
% 2.48/1.04  --prolific_symb_bound                   200
% 2.48/1.04  --lt_threshold                          2000
% 2.48/1.04  --clause_weak_htbl                      true
% 2.48/1.04  --gc_record_bc_elim                     false
% 2.48/1.04  
% 2.48/1.04  ------ Preprocessing Options
% 2.48/1.04  
% 2.48/1.04  --preprocessing_flag                    true
% 2.48/1.04  --time_out_prep_mult                    0.1
% 2.48/1.04  --splitting_mode                        input
% 2.48/1.04  --splitting_grd                         true
% 2.48/1.04  --splitting_cvd                         false
% 2.48/1.04  --splitting_cvd_svl                     false
% 2.48/1.04  --splitting_nvd                         32
% 2.48/1.04  --sub_typing                            true
% 2.48/1.04  --prep_gs_sim                           true
% 2.48/1.04  --prep_unflatten                        true
% 2.48/1.04  --prep_res_sim                          true
% 2.48/1.04  --prep_upred                            true
% 2.48/1.04  --prep_sem_filter                       exhaustive
% 2.48/1.04  --prep_sem_filter_out                   false
% 2.48/1.04  --pred_elim                             true
% 2.48/1.04  --res_sim_input                         true
% 2.48/1.04  --eq_ax_congr_red                       true
% 2.48/1.04  --pure_diseq_elim                       true
% 2.48/1.04  --brand_transform                       false
% 2.48/1.04  --non_eq_to_eq                          false
% 2.48/1.04  --prep_def_merge                        true
% 2.48/1.04  --prep_def_merge_prop_impl              false
% 2.48/1.04  --prep_def_merge_mbd                    true
% 2.48/1.04  --prep_def_merge_tr_red                 false
% 2.48/1.04  --prep_def_merge_tr_cl                  false
% 2.48/1.04  --smt_preprocessing                     true
% 2.48/1.04  --smt_ac_axioms                         fast
% 2.48/1.04  --preprocessed_out                      false
% 2.48/1.04  --preprocessed_stats                    false
% 2.48/1.04  
% 2.48/1.04  ------ Abstraction refinement Options
% 2.48/1.04  
% 2.48/1.04  --abstr_ref                             []
% 2.48/1.04  --abstr_ref_prep                        false
% 2.48/1.04  --abstr_ref_until_sat                   false
% 2.48/1.04  --abstr_ref_sig_restrict                funpre
% 2.48/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.04  --abstr_ref_under                       []
% 2.48/1.04  
% 2.48/1.04  ------ SAT Options
% 2.48/1.04  
% 2.48/1.04  --sat_mode                              false
% 2.48/1.04  --sat_fm_restart_options                ""
% 2.48/1.04  --sat_gr_def                            false
% 2.48/1.04  --sat_epr_types                         true
% 2.48/1.04  --sat_non_cyclic_types                  false
% 2.48/1.04  --sat_finite_models                     false
% 2.48/1.04  --sat_fm_lemmas                         false
% 2.48/1.04  --sat_fm_prep                           false
% 2.48/1.04  --sat_fm_uc_incr                        true
% 2.48/1.04  --sat_out_model                         small
% 2.48/1.04  --sat_out_clauses                       false
% 2.48/1.04  
% 2.48/1.04  ------ QBF Options
% 2.48/1.04  
% 2.48/1.04  --qbf_mode                              false
% 2.48/1.04  --qbf_elim_univ                         false
% 2.48/1.04  --qbf_dom_inst                          none
% 2.48/1.04  --qbf_dom_pre_inst                      false
% 2.48/1.04  --qbf_sk_in                             false
% 2.48/1.04  --qbf_pred_elim                         true
% 2.48/1.04  --qbf_split                             512
% 2.48/1.04  
% 2.48/1.04  ------ BMC1 Options
% 2.48/1.04  
% 2.48/1.04  --bmc1_incremental                      false
% 2.48/1.04  --bmc1_axioms                           reachable_all
% 2.48/1.04  --bmc1_min_bound                        0
% 2.48/1.04  --bmc1_max_bound                        -1
% 2.48/1.04  --bmc1_max_bound_default                -1
% 2.48/1.04  --bmc1_symbol_reachability              true
% 2.48/1.04  --bmc1_property_lemmas                  false
% 2.48/1.04  --bmc1_k_induction                      false
% 2.48/1.04  --bmc1_non_equiv_states                 false
% 2.48/1.04  --bmc1_deadlock                         false
% 2.48/1.04  --bmc1_ucm                              false
% 2.48/1.04  --bmc1_add_unsat_core                   none
% 2.48/1.04  --bmc1_unsat_core_children              false
% 2.48/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.04  --bmc1_out_stat                         full
% 2.48/1.04  --bmc1_ground_init                      false
% 2.48/1.04  --bmc1_pre_inst_next_state              false
% 2.48/1.04  --bmc1_pre_inst_state                   false
% 2.48/1.04  --bmc1_pre_inst_reach_state             false
% 2.48/1.04  --bmc1_out_unsat_core                   false
% 2.48/1.04  --bmc1_aig_witness_out                  false
% 2.48/1.04  --bmc1_verbose                          false
% 2.48/1.04  --bmc1_dump_clauses_tptp                false
% 2.48/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.04  --bmc1_dump_file                        -
% 2.48/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.04  --bmc1_ucm_extend_mode                  1
% 2.48/1.04  --bmc1_ucm_init_mode                    2
% 2.48/1.04  --bmc1_ucm_cone_mode                    none
% 2.48/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.04  --bmc1_ucm_relax_model                  4
% 2.48/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.04  --bmc1_ucm_layered_model                none
% 2.48/1.04  --bmc1_ucm_max_lemma_size               10
% 2.48/1.04  
% 2.48/1.04  ------ AIG Options
% 2.48/1.04  
% 2.48/1.04  --aig_mode                              false
% 2.48/1.04  
% 2.48/1.04  ------ Instantiation Options
% 2.48/1.04  
% 2.48/1.04  --instantiation_flag                    true
% 2.48/1.04  --inst_sos_flag                         false
% 2.48/1.04  --inst_sos_phase                        true
% 2.48/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.04  --inst_lit_sel_side                     none
% 2.48/1.04  --inst_solver_per_active                1400
% 2.48/1.04  --inst_solver_calls_frac                1.
% 2.48/1.04  --inst_passive_queue_type               priority_queues
% 2.48/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.04  --inst_passive_queues_freq              [25;2]
% 2.48/1.04  --inst_dismatching                      true
% 2.48/1.04  --inst_eager_unprocessed_to_passive     true
% 2.48/1.04  --inst_prop_sim_given                   true
% 2.48/1.04  --inst_prop_sim_new                     false
% 2.48/1.04  --inst_subs_new                         false
% 2.48/1.04  --inst_eq_res_simp                      false
% 2.48/1.04  --inst_subs_given                       false
% 2.48/1.04  --inst_orphan_elimination               true
% 2.48/1.04  --inst_learning_loop_flag               true
% 2.48/1.04  --inst_learning_start                   3000
% 2.48/1.04  --inst_learning_factor                  2
% 2.48/1.04  --inst_start_prop_sim_after_learn       3
% 2.48/1.04  --inst_sel_renew                        solver
% 2.48/1.04  --inst_lit_activity_flag                true
% 2.48/1.04  --inst_restr_to_given                   false
% 2.48/1.04  --inst_activity_threshold               500
% 2.48/1.04  --inst_out_proof                        true
% 2.48/1.04  
% 2.48/1.04  ------ Resolution Options
% 2.48/1.04  
% 2.48/1.04  --resolution_flag                       false
% 2.48/1.04  --res_lit_sel                           adaptive
% 2.48/1.04  --res_lit_sel_side                      none
% 2.48/1.04  --res_ordering                          kbo
% 2.48/1.04  --res_to_prop_solver                    active
% 2.48/1.04  --res_prop_simpl_new                    false
% 2.48/1.04  --res_prop_simpl_given                  true
% 2.48/1.04  --res_passive_queue_type                priority_queues
% 2.48/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.04  --res_passive_queues_freq               [15;5]
% 2.48/1.04  --res_forward_subs                      full
% 2.48/1.04  --res_backward_subs                     full
% 2.48/1.04  --res_forward_subs_resolution           true
% 2.48/1.04  --res_backward_subs_resolution          true
% 2.48/1.04  --res_orphan_elimination                true
% 2.48/1.04  --res_time_limit                        2.
% 2.48/1.04  --res_out_proof                         true
% 2.48/1.04  
% 2.48/1.04  ------ Superposition Options
% 2.48/1.04  
% 2.48/1.04  --superposition_flag                    true
% 2.48/1.04  --sup_passive_queue_type                priority_queues
% 2.48/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.04  --demod_completeness_check              fast
% 2.48/1.04  --demod_use_ground                      true
% 2.48/1.04  --sup_to_prop_solver                    passive
% 2.48/1.04  --sup_prop_simpl_new                    true
% 2.48/1.04  --sup_prop_simpl_given                  true
% 2.48/1.04  --sup_fun_splitting                     false
% 2.48/1.04  --sup_smt_interval                      50000
% 2.48/1.04  
% 2.48/1.04  ------ Superposition Simplification Setup
% 2.48/1.04  
% 2.48/1.04  --sup_indices_passive                   []
% 2.48/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.04  --sup_full_bw                           [BwDemod]
% 2.48/1.04  --sup_immed_triv                        [TrivRules]
% 2.48/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.04  --sup_immed_bw_main                     []
% 2.48/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.04  
% 2.48/1.04  ------ Combination Options
% 2.48/1.04  
% 2.48/1.04  --comb_res_mult                         3
% 2.48/1.04  --comb_sup_mult                         2
% 2.48/1.04  --comb_inst_mult                        10
% 2.48/1.04  
% 2.48/1.04  ------ Debug Options
% 2.48/1.04  
% 2.48/1.04  --dbg_backtrace                         false
% 2.48/1.04  --dbg_dump_prop_clauses                 false
% 2.48/1.04  --dbg_dump_prop_clauses_file            -
% 2.48/1.04  --dbg_out_stat                          false
% 2.48/1.04  
% 2.48/1.04  
% 2.48/1.04  
% 2.48/1.04  
% 2.48/1.04  ------ Proving...
% 2.48/1.04  
% 2.48/1.04  
% 2.48/1.04  % SZS status Theorem for theBenchmark.p
% 2.48/1.04  
% 2.48/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/1.04  
% 2.48/1.04  fof(f18,conjecture,(
% 2.48/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f19,negated_conjecture,(
% 2.48/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.48/1.04    inference(negated_conjecture,[],[f18])).
% 2.48/1.04  
% 2.48/1.04  fof(f35,plain,(
% 2.48/1.04    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.48/1.04    inference(ennf_transformation,[],[f19])).
% 2.48/1.04  
% 2.48/1.04  fof(f36,plain,(
% 2.48/1.04    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.48/1.04    inference(flattening,[],[f35])).
% 2.48/1.04  
% 2.48/1.04  fof(f43,plain,(
% 2.48/1.04    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.48/1.04    inference(nnf_transformation,[],[f36])).
% 2.48/1.04  
% 2.48/1.04  fof(f44,plain,(
% 2.48/1.04    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.48/1.04    inference(flattening,[],[f43])).
% 2.48/1.04  
% 2.48/1.04  fof(f45,plain,(
% 2.48/1.04    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.48/1.04    inference(rectify,[],[f44])).
% 2.48/1.04  
% 2.48/1.04  fof(f48,plain,(
% 2.48/1.04    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK4 & v3_pre_topc(sK4,X0) & r1_tarski(sK4,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.48/1.04    introduced(choice_axiom,[])).
% 2.48/1.04  
% 2.48/1.04  fof(f47,plain,(
% 2.48/1.04    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK3,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.48/1.04    introduced(choice_axiom,[])).
% 2.48/1.04  
% 2.48/1.04  fof(f46,plain,(
% 2.48/1.04    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(X1,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 2.48/1.04    introduced(choice_axiom,[])).
% 2.48/1.04  
% 2.48/1.04  fof(f49,plain,(
% 2.48/1.04    (((k1_xboole_0 != sK4 & v3_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(sK3,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 2.48/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).
% 2.48/1.04  
% 2.48/1.04  fof(f77,plain,(
% 2.48/1.04    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tops_1(sK3,sK2)),
% 2.48/1.04    inference(cnf_transformation,[],[f49])).
% 2.48/1.04  
% 2.48/1.04  fof(f75,plain,(
% 2.48/1.04    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.48/1.04    inference(cnf_transformation,[],[f49])).
% 2.48/1.04  
% 2.48/1.04  fof(f17,axiom,(
% 2.48/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f34,plain,(
% 2.48/1.04    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/1.04    inference(ennf_transformation,[],[f17])).
% 2.48/1.04  
% 2.48/1.04  fof(f42,plain,(
% 2.48/1.04    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/1.04    inference(nnf_transformation,[],[f34])).
% 2.48/1.04  
% 2.48/1.04  fof(f71,plain,(
% 2.48/1.04    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f42])).
% 2.48/1.04  
% 2.48/1.04  fof(f74,plain,(
% 2.48/1.04    l1_pre_topc(sK2)),
% 2.48/1.04    inference(cnf_transformation,[],[f49])).
% 2.48/1.04  
% 2.48/1.04  fof(f12,axiom,(
% 2.48/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f26,plain,(
% 2.48/1.04    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.48/1.04    inference(ennf_transformation,[],[f12])).
% 2.48/1.04  
% 2.48/1.04  fof(f27,plain,(
% 2.48/1.04    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/1.04    inference(flattening,[],[f26])).
% 2.48/1.04  
% 2.48/1.04  fof(f64,plain,(
% 2.48/1.04    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f27])).
% 2.48/1.04  
% 2.48/1.04  fof(f73,plain,(
% 2.48/1.04    v2_pre_topc(sK2)),
% 2.48/1.04    inference(cnf_transformation,[],[f49])).
% 2.48/1.04  
% 2.48/1.04  fof(f14,axiom,(
% 2.48/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f29,plain,(
% 2.48/1.04    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/1.04    inference(ennf_transformation,[],[f14])).
% 2.48/1.04  
% 2.48/1.04  fof(f67,plain,(
% 2.48/1.04    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f29])).
% 2.48/1.04  
% 2.48/1.04  fof(f9,axiom,(
% 2.48/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f37,plain,(
% 2.48/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.48/1.04    inference(nnf_transformation,[],[f9])).
% 2.48/1.04  
% 2.48/1.04  fof(f58,plain,(
% 2.48/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.48/1.04    inference(cnf_transformation,[],[f37])).
% 2.48/1.04  
% 2.48/1.04  fof(f3,axiom,(
% 2.48/1.04    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f21,plain,(
% 2.48/1.04    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.48/1.04    inference(ennf_transformation,[],[f3])).
% 2.48/1.04  
% 2.48/1.04  fof(f22,plain,(
% 2.48/1.04    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.48/1.04    inference(flattening,[],[f21])).
% 2.48/1.04  
% 2.48/1.04  fof(f52,plain,(
% 2.48/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f22])).
% 2.48/1.04  
% 2.48/1.04  fof(f76,plain,(
% 2.48/1.04    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f49])).
% 2.48/1.04  
% 2.48/1.04  fof(f59,plain,(
% 2.48/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f37])).
% 2.48/1.04  
% 2.48/1.04  fof(f15,axiom,(
% 2.48/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f30,plain,(
% 2.48/1.04    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/1.04    inference(ennf_transformation,[],[f15])).
% 2.48/1.04  
% 2.48/1.04  fof(f31,plain,(
% 2.48/1.04    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/1.04    inference(flattening,[],[f30])).
% 2.48/1.04  
% 2.48/1.04  fof(f68,plain,(
% 2.48/1.04    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f31])).
% 2.48/1.04  
% 2.48/1.04  fof(f16,axiom,(
% 2.48/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f32,plain,(
% 2.48/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.48/1.04    inference(ennf_transformation,[],[f16])).
% 2.48/1.04  
% 2.48/1.04  fof(f33,plain,(
% 2.48/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/1.04    inference(flattening,[],[f32])).
% 2.48/1.04  
% 2.48/1.04  fof(f69,plain,(
% 2.48/1.04    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f33])).
% 2.48/1.04  
% 2.48/1.04  fof(f70,plain,(
% 2.48/1.04    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f33])).
% 2.48/1.04  
% 2.48/1.04  fof(f79,plain,(
% 2.48/1.04    v3_pre_topc(sK4,sK2) | ~v2_tops_1(sK3,sK2)),
% 2.48/1.04    inference(cnf_transformation,[],[f49])).
% 2.48/1.04  
% 2.48/1.04  fof(f72,plain,(
% 2.48/1.04    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f42])).
% 2.48/1.04  
% 2.48/1.04  fof(f78,plain,(
% 2.48/1.04    r1_tarski(sK4,sK3) | ~v2_tops_1(sK3,sK2)),
% 2.48/1.04    inference(cnf_transformation,[],[f49])).
% 2.48/1.04  
% 2.48/1.04  fof(f4,axiom,(
% 2.48/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f23,plain,(
% 2.48/1.04    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.48/1.04    inference(ennf_transformation,[],[f4])).
% 2.48/1.04  
% 2.48/1.04  fof(f53,plain,(
% 2.48/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f23])).
% 2.48/1.04  
% 2.48/1.04  fof(f5,axiom,(
% 2.48/1.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f54,plain,(
% 2.48/1.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f5])).
% 2.48/1.04  
% 2.48/1.04  fof(f7,axiom,(
% 2.48/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f56,plain,(
% 2.48/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.48/1.04    inference(cnf_transformation,[],[f7])).
% 2.48/1.04  
% 2.48/1.04  fof(f8,axiom,(
% 2.48/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.48/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.04  
% 2.48/1.04  fof(f57,plain,(
% 2.48/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.48/1.04    inference(cnf_transformation,[],[f8])).
% 2.48/1.04  
% 2.48/1.04  fof(f80,plain,(
% 2.48/1.04    k1_xboole_0 != sK4 | ~v2_tops_1(sK3,sK2)),
% 2.48/1.04    inference(cnf_transformation,[],[f49])).
% 2.48/1.04  
% 2.48/1.04  cnf(c_25,negated_conjecture,
% 2.48/1.04      ( ~ v2_tops_1(sK3,sK2)
% 2.48/1.04      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.48/1.04      inference(cnf_transformation,[],[f77]) ).
% 2.48/1.04  
% 2.48/1.04  cnf(c_2152,plain,
% 2.48/1.04      ( v2_tops_1(sK3,sK2) != iProver_top
% 2.48/1.04      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.48/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.48/1.04  
% 2.48/1.04  cnf(c_27,negated_conjecture,
% 2.48/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.48/1.04      inference(cnf_transformation,[],[f75]) ).
% 2.48/1.04  
% 2.48/1.04  cnf(c_2150,plain,
% 2.48/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.48/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.48/1.04  
% 2.48/1.04  cnf(c_21,plain,
% 2.48/1.04      ( ~ v2_tops_1(X0,X1)
% 2.48/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.04      | ~ l1_pre_topc(X1)
% 2.48/1.04      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.48/1.04      inference(cnf_transformation,[],[f71]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_28,negated_conjecture,
% 2.48/1.05      ( l1_pre_topc(sK2) ),
% 2.48/1.05      inference(cnf_transformation,[],[f74]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_525,plain,
% 2.48/1.05      ( ~ v2_tops_1(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.48/1.05      | sK2 != X1 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_526,plain,
% 2.48/1.05      ( ~ v2_tops_1(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,X0) = k1_xboole_0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_525]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2142,plain,
% 2.48/1.05      ( k1_tops_1(sK2,X0) = k1_xboole_0
% 2.48/1.05      | v2_tops_1(X0,sK2) != iProver_top
% 2.48/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3398,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 2.48/1.05      | v2_tops_1(sK3,sK2) != iProver_top ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_2150,c_2142]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_13,plain,
% 2.48/1.05      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/1.05      | ~ v2_pre_topc(X0)
% 2.48/1.05      | ~ l1_pre_topc(X0) ),
% 2.48/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_29,negated_conjecture,
% 2.48/1.05      ( v2_pre_topc(sK2) ),
% 2.48/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_410,plain,
% 2.48/1.05      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/1.05      | ~ l1_pre_topc(X0)
% 2.48/1.05      | sK2 != X0 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_411,plain,
% 2.48/1.05      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ l1_pre_topc(sK2) ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_410]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_415,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_411,c_28]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_416,plain,
% 2.48/1.05      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.48/1.05      inference(renaming,[status(thm)],[c_415]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2343,plain,
% 2.48/1.05      ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
% 2.48/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_416]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_16,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.48/1.05      | ~ l1_pre_topc(X1) ),
% 2.48/1.05      inference(cnf_transformation,[],[f67]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_573,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.48/1.05      | sK2 != X1 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_574,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_573]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2361,plain,
% 2.48/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_574]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_8,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.48/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2394,plain,
% 2.48/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | r1_tarski(sK3,u1_struct_0(sK2)) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_8]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_1552,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2467,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) != X0
% 2.48/1.05      | k1_tops_1(sK2,sK3) = k1_xboole_0
% 2.48/1.05      | k1_xboole_0 != X0 ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_1552]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2743,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) != k1_tops_1(sK2,sK3)
% 2.48/1.05      | k1_tops_1(sK2,sK3) = k1_xboole_0
% 2.48/1.05      | k1_xboole_0 != k1_tops_1(sK2,sK3) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_2467]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_1551,plain,( X0 = X0 ),theory(equality) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2744,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) = k1_tops_1(sK2,sK3) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_1551]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2,plain,
% 2.48/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.48/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2470,plain,
% 2.48/1.05      ( r1_tarski(k1_tops_1(sK2,sK3),X0)
% 2.48/1.05      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 2.48/1.05      | ~ r1_tarski(sK3,X0) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_2]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2748,plain,
% 2.48/1.05      ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2))
% 2.48/1.05      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 2.48/1.05      | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_2470]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_26,negated_conjecture,
% 2.48/1.05      ( v2_tops_1(sK3,sK2)
% 2.48/1.05      | ~ v3_pre_topc(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ r1_tarski(X0,sK3)
% 2.48/1.05      | k1_xboole_0 = X0 ),
% 2.48/1.05      inference(cnf_transformation,[],[f76]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2886,plain,
% 2.48/1.05      ( v2_tops_1(sK3,sK2)
% 2.48/1.05      | ~ v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
% 2.48/1.05      | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 2.48/1.05      | k1_xboole_0 = k1_tops_1(sK2,sK3) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_26]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_7,plain,
% 2.48/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.48/1.05      inference(cnf_transformation,[],[f59]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3045,plain,
% 2.48/1.05      ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_7]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3415,plain,
% 2.48/1.05      ( ~ v2_tops_1(sK3,sK2) | k1_tops_1(sK2,sK3) = k1_xboole_0 ),
% 2.48/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_3398]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3501,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_3398,c_27,c_2343,c_2361,c_2394,c_2743,c_2744,c_2748,
% 2.48/1.05                 c_2886,c_3045,c_3415]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_17,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ r1_tarski(X0,X2)
% 2.48/1.05      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.48/1.05      | ~ l1_pre_topc(X1) ),
% 2.48/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_555,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ r1_tarski(X0,X2)
% 2.48/1.05      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.48/1.05      | sK2 != X1 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_556,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ r1_tarski(X0,X1)
% 2.48/1.05      | r1_tarski(k1_tops_1(sK2,X0),k1_tops_1(sK2,X1)) ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_555]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2140,plain,
% 2.48/1.05      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | r1_tarski(X0,X1) != iProver_top
% 2.48/1.05      | r1_tarski(k1_tops_1(sK2,X0),k1_tops_1(sK2,X1)) = iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3763,plain,
% 2.48/1.05      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | r1_tarski(X0,sK3) != iProver_top
% 2.48/1.05      | r1_tarski(k1_tops_1(sK2,X0),k1_xboole_0) = iProver_top ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_3501,c_2140]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_32,plain,
% 2.48/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_7399,plain,
% 2.48/1.05      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | r1_tarski(X0,sK3) != iProver_top
% 2.48/1.05      | r1_tarski(k1_tops_1(sK2,X0),k1_xboole_0) = iProver_top ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_3763,c_32]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_7409,plain,
% 2.48/1.05      ( v2_tops_1(sK3,sK2) != iProver_top
% 2.48/1.05      | r1_tarski(k1_tops_1(sK2,sK4),k1_xboole_0) = iProver_top
% 2.48/1.05      | r1_tarski(sK4,sK3) != iProver_top ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_2152,c_7399]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_19,plain,
% 2.48/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ v2_pre_topc(X3)
% 2.48/1.05      | ~ l1_pre_topc(X3)
% 2.48/1.05      | ~ l1_pre_topc(X1)
% 2.48/1.05      | k1_tops_1(X1,X0) = X0 ),
% 2.48/1.05      inference(cnf_transformation,[],[f69]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_453,plain,
% 2.48/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.48/1.05      | ~ l1_pre_topc(X1)
% 2.48/1.05      | ~ l1_pre_topc(X3)
% 2.48/1.05      | k1_tops_1(X1,X0) = X0
% 2.48/1.05      | sK2 != X3 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_454,plain,
% 2.48/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ l1_pre_topc(X1)
% 2.48/1.05      | ~ l1_pre_topc(sK2)
% 2.48/1.05      | k1_tops_1(X1,X0) = X0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_453]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_458,plain,
% 2.48/1.05      ( ~ l1_pre_topc(X1)
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ v3_pre_topc(X0,X1)
% 2.48/1.05      | k1_tops_1(X1,X0) = X0 ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_454,c_28]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_459,plain,
% 2.48/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ l1_pre_topc(X1)
% 2.48/1.05      | k1_tops_1(X1,X0) = X0 ),
% 2.48/1.05      inference(renaming,[status(thm)],[c_458]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_507,plain,
% 2.48/1.05      ( ~ v3_pre_topc(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(X1,X0) = X0
% 2.48/1.05      | sK2 != X1 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_459,c_28]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_508,plain,
% 2.48/1.05      ( ~ v3_pre_topc(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,X0) = X0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_507]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_1548,plain,
% 2.48/1.05      ( ~ v3_pre_topc(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,X0) = X0
% 2.48/1.05      | ~ sP2_iProver_split ),
% 2.48/1.05      inference(splitting,
% 2.48/1.05                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.48/1.05                [c_508]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2144,plain,
% 2.48/1.05      ( k1_tops_1(sK2,X0) = X0
% 2.48/1.05      | v3_pre_topc(X0,sK2) != iProver_top
% 2.48/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | sP2_iProver_split != iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_1548]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_1549,plain,
% 2.48/1.05      ( sP2_iProver_split | sP0_iProver_split ),
% 2.48/1.05      inference(splitting,
% 2.48/1.05                [splitting(split),new_symbols(definition,[])],
% 2.48/1.05                [c_508]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_1588,plain,
% 2.48/1.05      ( sP2_iProver_split = iProver_top
% 2.48/1.05      | sP0_iProver_split = iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_1549]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_1589,plain,
% 2.48/1.05      ( k1_tops_1(sK2,X0) = X0
% 2.48/1.05      | v3_pre_topc(X0,sK2) != iProver_top
% 2.48/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | sP2_iProver_split != iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_1548]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_18,plain,
% 2.48/1.05      ( v3_pre_topc(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.48/1.05      | ~ v2_pre_topc(X1)
% 2.48/1.05      | ~ l1_pre_topc(X1)
% 2.48/1.05      | ~ l1_pre_topc(X3)
% 2.48/1.05      | k1_tops_1(X1,X0) != X0 ),
% 2.48/1.05      inference(cnf_transformation,[],[f70]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_428,plain,
% 2.48/1.05      ( v3_pre_topc(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.48/1.05      | ~ l1_pre_topc(X1)
% 2.48/1.05      | ~ l1_pre_topc(X3)
% 2.48/1.05      | k1_tops_1(X1,X0) != X0
% 2.48/1.05      | sK2 != X1 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_429,plain,
% 2.48/1.05      ( v3_pre_topc(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ l1_pre_topc(X2)
% 2.48/1.05      | ~ l1_pre_topc(sK2)
% 2.48/1.05      | k1_tops_1(sK2,X0) != X0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_428]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_433,plain,
% 2.48/1.05      ( ~ l1_pre_topc(X2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.05      | v3_pre_topc(X0,sK2)
% 2.48/1.05      | k1_tops_1(sK2,X0) != X0 ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_429,c_28]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_434,plain,
% 2.48/1.05      ( v3_pre_topc(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ l1_pre_topc(X2)
% 2.48/1.05      | k1_tops_1(sK2,X0) != X0 ),
% 2.48/1.05      inference(renaming,[status(thm)],[c_433]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_585,plain,
% 2.48/1.05      ( v3_pre_topc(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,X0) != X0
% 2.48/1.05      | sK2 != X2 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_28,c_434]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_586,plain,
% 2.48/1.05      ( v3_pre_topc(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,X0) != X0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_585]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_1545,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | ~ sP0_iProver_split ),
% 2.48/1.05      inference(splitting,
% 2.48/1.05                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.48/1.05                [c_586]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2138,plain,
% 2.48/1.05      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | sP0_iProver_split != iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2757,plain,
% 2.48/1.05      ( sP0_iProver_split != iProver_top ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_2150,c_2138]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3670,plain,
% 2.48/1.05      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.48/1.05      | v3_pre_topc(X0,sK2) != iProver_top
% 2.48/1.05      | k1_tops_1(sK2,X0) = X0 ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_2144,c_1588,c_1589,c_2757]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3671,plain,
% 2.48/1.05      ( k1_tops_1(sK2,X0) = X0
% 2.48/1.05      | v3_pre_topc(X0,sK2) != iProver_top
% 2.48/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.48/1.05      inference(renaming,[status(thm)],[c_3670]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3677,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK4) = sK4
% 2.48/1.05      | v2_tops_1(sK3,sK2) != iProver_top
% 2.48/1.05      | v3_pre_topc(sK4,sK2) != iProver_top ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_2152,c_3671]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_23,negated_conjecture,
% 2.48/1.05      ( ~ v2_tops_1(sK3,sK2) | v3_pre_topc(sK4,sK2) ),
% 2.48/1.05      inference(cnf_transformation,[],[f79]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_20,plain,
% 2.48/1.05      ( v2_tops_1(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | ~ l1_pre_topc(X1)
% 2.48/1.05      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.48/1.05      inference(cnf_transformation,[],[f72]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_540,plain,
% 2.48/1.05      ( v2_tops_1(X0,X1)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.05      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.48/1.05      | sK2 != X1 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_541,plain,
% 2.48/1.05      ( v2_tops_1(X0,sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,X0) != k1_xboole_0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_540]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_919,plain,
% 2.48/1.05      ( v3_pre_topc(sK4,sK2)
% 2.48/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,X0) != k1_xboole_0
% 2.48/1.05      | sK2 != sK2
% 2.48/1.05      | sK3 != X0 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_23,c_541]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_920,plain,
% 2.48/1.05      ( v3_pre_topc(sK4,sK2)
% 2.48/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_919]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_922,plain,
% 2.48/1.05      ( v3_pre_topc(sK4,sK2) | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_920,c_27]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_924,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 2.48/1.05      | v3_pre_topc(sK4,sK2) = iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2357,plain,
% 2.48/1.05      ( v2_tops_1(sK3,sK2)
% 2.48/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.48/1.05      inference(instantiation,[status(thm)],[c_541]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2358,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 2.48/1.05      | v2_tops_1(sK3,sK2) = iProver_top
% 2.48/1.05      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_2357]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_4128,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK4) = sK4 ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_3677,c_27,c_32,c_924,c_2343,c_2358,c_2361,c_2394,
% 2.48/1.05                 c_2743,c_2744,c_2748,c_2886,c_3045,c_3415]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_7421,plain,
% 2.48/1.05      ( v2_tops_1(sK3,sK2) != iProver_top
% 2.48/1.05      | r1_tarski(sK4,sK3) != iProver_top
% 2.48/1.05      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.48/1.05      inference(light_normalisation,[status(thm)],[c_7409,c_4128]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_24,negated_conjecture,
% 2.48/1.05      ( ~ v2_tops_1(sK3,sK2) | r1_tarski(sK4,sK3) ),
% 2.48/1.05      inference(cnf_transformation,[],[f78]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_905,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | r1_tarski(sK4,sK3)
% 2.48/1.05      | k1_tops_1(sK2,X0) != k1_xboole_0
% 2.48/1.05      | sK2 != sK2
% 2.48/1.05      | sK3 != X0 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_24,c_541]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_906,plain,
% 2.48/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | r1_tarski(sK4,sK3)
% 2.48/1.05      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_905]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_908,plain,
% 2.48/1.05      ( r1_tarski(sK4,sK3) | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_906,c_27]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_910,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 2.48/1.05      | r1_tarski(sK4,sK3) = iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_908]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_7783,plain,
% 2.48/1.05      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_7421,c_27,c_32,c_910,c_2343,c_2358,c_2361,c_2394,
% 2.48/1.05                 c_2743,c_2744,c_2748,c_2886,c_3045,c_3415]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3,plain,
% 2.48/1.05      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.48/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2159,plain,
% 2.48/1.05      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_7789,plain,
% 2.48/1.05      ( k3_xboole_0(sK4,k1_xboole_0) = sK4 ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_7783,c_2159]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_4,plain,
% 2.48/1.05      ( r1_tarski(k1_xboole_0,X0) ),
% 2.48/1.05      inference(cnf_transformation,[],[f54]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2158,plain,
% 2.48/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.48/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3228,plain,
% 2.48/1.05      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_2158,c_2159]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_5,plain,
% 2.48/1.05      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.48/1.05      inference(cnf_transformation,[],[f56]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_6,plain,
% 2.48/1.05      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 2.48/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_2673,plain,
% 2.48/1.05      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_3123,plain,
% 2.48/1.05      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_2673,c_6]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_5614,plain,
% 2.48/1.05      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.48/1.05      inference(superposition,[status(thm)],[c_3228,c_3123]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_7791,plain,
% 2.48/1.05      ( sK4 = k1_xboole_0 ),
% 2.48/1.05      inference(demodulation,[status(thm)],[c_7789,c_5614]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_22,negated_conjecture,
% 2.48/1.05      ( ~ v2_tops_1(sK3,sK2) | k1_xboole_0 != sK4 ),
% 2.48/1.05      inference(cnf_transformation,[],[f80]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_933,plain,
% 2.48/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,X0) != k1_xboole_0
% 2.48/1.05      | sK2 != sK2
% 2.48/1.05      | sK3 != X0
% 2.48/1.05      | sK4 != k1_xboole_0 ),
% 2.48/1.05      inference(resolution_lifted,[status(thm)],[c_22,c_541]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_934,plain,
% 2.48/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.48/1.05      | k1_tops_1(sK2,sK3) != k1_xboole_0
% 2.48/1.05      | sK4 != k1_xboole_0 ),
% 2.48/1.05      inference(unflattening,[status(thm)],[c_933]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(c_936,plain,
% 2.48/1.05      ( k1_tops_1(sK2,sK3) != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 2.48/1.05      inference(global_propositional_subsumption,
% 2.48/1.05                [status(thm)],
% 2.48/1.05                [c_934,c_27]) ).
% 2.48/1.05  
% 2.48/1.05  cnf(contradiction,plain,
% 2.48/1.05      ( $false ),
% 2.48/1.05      inference(minisat,[status(thm)],[c_7791,c_3501,c_936]) ).
% 2.48/1.05  
% 2.48/1.05  
% 2.48/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.05  
% 2.48/1.05  ------                               Statistics
% 2.48/1.05  
% 2.48/1.05  ------ General
% 2.48/1.05  
% 2.48/1.05  abstr_ref_over_cycles:                  0
% 2.48/1.05  abstr_ref_under_cycles:                 0
% 2.48/1.05  gc_basic_clause_elim:                   0
% 2.48/1.05  forced_gc_time:                         0
% 2.48/1.05  parsing_time:                           0.009
% 2.48/1.05  unif_index_cands_time:                  0.
% 2.48/1.05  unif_index_add_time:                    0.
% 2.48/1.05  orderings_time:                         0.
% 2.48/1.05  out_proof_time:                         0.015
% 2.48/1.05  total_time:                             0.199
% 2.48/1.05  num_of_symbols:                         55
% 2.48/1.05  num_of_terms:                           7007
% 2.48/1.05  
% 2.48/1.05  ------ Preprocessing
% 2.48/1.05  
% 2.48/1.05  num_of_splits:                          4
% 2.48/1.05  num_of_split_atoms:                     3
% 2.48/1.05  num_of_reused_defs:                     1
% 2.48/1.05  num_eq_ax_congr_red:                    26
% 2.48/1.05  num_of_sem_filtered_clauses:            4
% 2.48/1.05  num_of_subtypes:                        0
% 2.48/1.05  monotx_restored_types:                  0
% 2.48/1.05  sat_num_of_epr_types:                   0
% 2.48/1.05  sat_num_of_non_cyclic_types:            0
% 2.48/1.05  sat_guarded_non_collapsed_types:        0
% 2.48/1.05  num_pure_diseq_elim:                    0
% 2.48/1.05  simp_replaced_by:                       0
% 2.48/1.05  res_preprocessed:                       143
% 2.48/1.05  prep_upred:                             0
% 2.48/1.05  prep_unflattend:                        37
% 2.48/1.05  smt_new_axioms:                         0
% 2.48/1.05  pred_elim_cands:                        4
% 2.48/1.05  pred_elim:                              3
% 2.48/1.05  pred_elim_cl:                           3
% 2.48/1.05  pred_elim_cycles:                       7
% 2.48/1.05  merged_defs:                            8
% 2.48/1.05  merged_defs_ncl:                        0
% 2.48/1.05  bin_hyper_res:                          8
% 2.48/1.05  prep_cycles:                            4
% 2.48/1.05  pred_elim_time:                         0.012
% 2.48/1.05  splitting_time:                         0.
% 2.48/1.05  sem_filter_time:                        0.
% 2.48/1.05  monotx_time:                            0.
% 2.48/1.05  subtype_inf_time:                       0.
% 2.48/1.05  
% 2.48/1.05  ------ Problem properties
% 2.48/1.05  
% 2.48/1.05  clauses:                                31
% 2.48/1.05  conjectures:                            6
% 2.48/1.05  epr:                                    7
% 2.48/1.05  horn:                                   28
% 2.48/1.05  ground:                                 9
% 2.48/1.05  unary:                                  7
% 2.48/1.05  binary:                                 17
% 2.48/1.05  lits:                                   67
% 2.48/1.05  lits_eq:                                15
% 2.48/1.05  fd_pure:                                0
% 2.48/1.05  fd_pseudo:                              0
% 2.48/1.05  fd_cond:                                4
% 2.48/1.05  fd_pseudo_cond:                         0
% 2.48/1.05  ac_symbols:                             0
% 2.48/1.05  
% 2.48/1.05  ------ Propositional Solver
% 2.48/1.05  
% 2.48/1.05  prop_solver_calls:                      28
% 2.48/1.05  prop_fast_solver_calls:                 1110
% 2.48/1.05  smt_solver_calls:                       0
% 2.48/1.05  smt_fast_solver_calls:                  0
% 2.48/1.05  prop_num_of_clauses:                    3011
% 2.48/1.05  prop_preprocess_simplified:             8307
% 2.48/1.05  prop_fo_subsumed:                       50
% 2.48/1.05  prop_solver_time:                       0.
% 2.48/1.05  smt_solver_time:                        0.
% 2.48/1.05  smt_fast_solver_time:                   0.
% 2.48/1.05  prop_fast_solver_time:                  0.
% 2.48/1.05  prop_unsat_core_time:                   0.
% 2.48/1.05  
% 2.48/1.05  ------ QBF
% 2.48/1.05  
% 2.48/1.05  qbf_q_res:                              0
% 2.48/1.05  qbf_num_tautologies:                    0
% 2.48/1.05  qbf_prep_cycles:                        0
% 2.48/1.05  
% 2.48/1.05  ------ BMC1
% 2.48/1.05  
% 2.48/1.05  bmc1_current_bound:                     -1
% 2.48/1.05  bmc1_last_solved_bound:                 -1
% 2.48/1.05  bmc1_unsat_core_size:                   -1
% 2.48/1.05  bmc1_unsat_core_parents_size:           -1
% 2.48/1.05  bmc1_merge_next_fun:                    0
% 2.48/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.48/1.05  
% 2.48/1.05  ------ Instantiation
% 2.48/1.05  
% 2.48/1.05  inst_num_of_clauses:                    866
% 2.48/1.05  inst_num_in_passive:                    313
% 2.48/1.05  inst_num_in_active:                     403
% 2.48/1.05  inst_num_in_unprocessed:                150
% 2.48/1.05  inst_num_of_loops:                      430
% 2.48/1.05  inst_num_of_learning_restarts:          0
% 2.48/1.05  inst_num_moves_active_passive:          24
% 2.48/1.05  inst_lit_activity:                      0
% 2.48/1.05  inst_lit_activity_moves:                0
% 2.48/1.05  inst_num_tautologies:                   0
% 2.48/1.05  inst_num_prop_implied:                  0
% 2.48/1.05  inst_num_existing_simplified:           0
% 2.48/1.05  inst_num_eq_res_simplified:             0
% 2.48/1.05  inst_num_child_elim:                    0
% 2.48/1.05  inst_num_of_dismatching_blockings:      44
% 2.48/1.05  inst_num_of_non_proper_insts:           607
% 2.48/1.05  inst_num_of_duplicates:                 0
% 2.48/1.05  inst_inst_num_from_inst_to_res:         0
% 2.48/1.05  inst_dismatching_checking_time:         0.
% 2.48/1.05  
% 2.48/1.05  ------ Resolution
% 2.48/1.05  
% 2.48/1.05  res_num_of_clauses:                     0
% 2.48/1.05  res_num_in_passive:                     0
% 2.48/1.05  res_num_in_active:                      0
% 2.48/1.05  res_num_of_loops:                       147
% 2.48/1.05  res_forward_subset_subsumed:            53
% 2.48/1.05  res_backward_subset_subsumed:           0
% 2.48/1.05  res_forward_subsumed:                   0
% 2.48/1.05  res_backward_subsumed:                  0
% 2.48/1.05  res_forward_subsumption_resolution:     0
% 2.48/1.05  res_backward_subsumption_resolution:    0
% 2.48/1.05  res_clause_to_clause_subsumption:       468
% 2.48/1.05  res_orphan_elimination:                 0
% 2.48/1.05  res_tautology_del:                      77
% 2.48/1.05  res_num_eq_res_simplified:              0
% 2.48/1.05  res_num_sel_changes:                    0
% 2.48/1.05  res_moves_from_active_to_pass:          0
% 2.48/1.05  
% 2.48/1.05  ------ Superposition
% 2.48/1.05  
% 2.48/1.05  sup_time_total:                         0.
% 2.48/1.05  sup_time_generating:                    0.
% 2.48/1.05  sup_time_sim_full:                      0.
% 2.48/1.05  sup_time_sim_immed:                     0.
% 2.48/1.05  
% 2.48/1.05  sup_num_of_clauses:                     162
% 2.48/1.05  sup_num_in_active:                      77
% 2.48/1.05  sup_num_in_passive:                     85
% 2.48/1.05  sup_num_of_loops:                       85
% 2.48/1.05  sup_fw_superposition:                   109
% 2.48/1.05  sup_bw_superposition:                   155
% 2.48/1.05  sup_immediate_simplified:               84
% 2.48/1.05  sup_given_eliminated:                   3
% 2.48/1.05  comparisons_done:                       0
% 2.48/1.05  comparisons_avoided:                    0
% 2.48/1.05  
% 2.48/1.05  ------ Simplifications
% 2.48/1.05  
% 2.48/1.05  
% 2.48/1.05  sim_fw_subset_subsumed:                 9
% 2.48/1.05  sim_bw_subset_subsumed:                 1
% 2.48/1.05  sim_fw_subsumed:                        14
% 2.48/1.05  sim_bw_subsumed:                        1
% 2.48/1.05  sim_fw_subsumption_res:                 0
% 2.48/1.05  sim_bw_subsumption_res:                 0
% 2.48/1.05  sim_tautology_del:                      5
% 2.48/1.05  sim_eq_tautology_del:                   15
% 2.48/1.05  sim_eq_res_simp:                        0
% 2.48/1.05  sim_fw_demodulated:                     14
% 2.48/1.05  sim_bw_demodulated:                     12
% 2.48/1.05  sim_light_normalised:                   67
% 2.48/1.05  sim_joinable_taut:                      0
% 2.48/1.05  sim_joinable_simp:                      0
% 2.48/1.05  sim_ac_normalised:                      0
% 2.48/1.05  sim_smt_subsumption:                    0
% 2.48/1.05  
%------------------------------------------------------------------------------

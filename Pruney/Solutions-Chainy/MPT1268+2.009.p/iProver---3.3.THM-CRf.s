%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:03 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  203 (1047 expanded)
%              Number of clauses        :  125 ( 282 expanded)
%              Number of leaves         :   22 ( 267 expanded)
%              Depth                    :   27
%              Number of atoms          :  700 (6900 expanded)
%              Number of equality atoms :  220 (1384 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f52,f63,f63])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f58,f63])).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f50,f49,f48])).

fof(f85,plain,
    ( k1_xboole_0 != sK4
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                & r1_tarski(sK1(X0,X1,X2),X2)
                & v3_pre_topc(sK1(X0,X1,X2),X0)
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK2)
      | ~ r1_tarski(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tops_1(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,
    ( r1_tarski(sK4,sK3)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2561,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3129,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_4120,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_3129])).

cnf(c_5732,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_4120])).

cnf(c_9373,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_5732])).

cnf(c_10219,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_9373])).

cnf(c_11054,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10,c_10219])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11066,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k2_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0))) ),
    inference(light_normalisation,[status(thm)],[c_11054,c_9])).

cnf(c_11067,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11066,c_10,c_3129])).

cnf(c_11108,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0))) ),
    inference(superposition,[status(thm)],[c_11067,c_3129])).

cnf(c_11119,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0))) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_11108,c_0,c_9])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2560,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4180,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_2560])).

cnf(c_6539,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_4180])).

cnf(c_6793,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_6539])).

cnf(c_11309,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k2_xboole_0(X0,X1))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11119,c_6793])).

cnf(c_11366,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k1_xboole_0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11309,c_11067])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2582,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_9])).

cnf(c_11367,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11366,c_9,c_2582])).

cnf(c_12657,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_11367])).

cnf(c_12665,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12657,c_9,c_10])).

cnf(c_25,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_42,plain,
    ( k1_xboole_0 != sK4
    | v2_tops_1(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3662,plain,
    ( ~ r1_tarski(sK4,k4_xboole_0(X0,sK4))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3663,plain,
    ( k1_xboole_0 = sK4
    | r1_tarski(sK4,k4_xboole_0(X0,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3662])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_460,plain,
    ( ~ r2_hidden(X1,k1_tops_1(sK2,X0))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_31])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_460])).

cnf(c_2548,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_29,negated_conjecture,
    ( v2_tops_1(sK3,sK2)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2552,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK3,sK2) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3805,plain,
    ( sK1(sK2,X0,X1) = k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top
    | v3_pre_topc(sK1(sK2,X0,X1),sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,X1)) != iProver_top
    | r1_tarski(sK1(sK2,X0,X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_2552])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_640,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_641,plain,
    ( v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_2791,plain,
    ( v2_tops_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_2792,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2791])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_2794,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_2795,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2794])).

cnf(c_2551,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_412,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_413,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_31])).

cnf(c_418,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_2549,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_3197,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_2549])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2559,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4831,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK3,sK2) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2559,c_2552])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3028,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3866,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3028])).

cnf(c_3867,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3866])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3041,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK2))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4742,plain,
    ( r1_tarski(X0,u1_struct_0(sK2))
    | ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3041])).

cnf(c_4743,plain,
    ( r1_tarski(X0,u1_struct_0(sK2)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4742])).

cnf(c_5210,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v2_tops_1(sK3,sK2) = iProver_top
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4831,c_35,c_3867,c_4743])).

cnf(c_5211,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK3,sK2) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5210])).

cnf(c_5221,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3197,c_5211])).

cnf(c_5285,plain,
    ( v2_tops_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3805,c_35,c_2792,c_2795,c_5221])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2564,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_28,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2553,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_518,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_519,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_521,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_31])).

cnf(c_522,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_521])).

cnf(c_2545,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_3958,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_2545])).

cnf(c_39,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | v3_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_969,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X0,X1)
    | sK2 != sK2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_522])).

cnf(c_970,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ r2_hidden(X1,sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_969])).

cnf(c_971,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_4394,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3958,c_39,c_971])).

cnf(c_4404,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_4394])).

cnf(c_27,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_40,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4526,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | v2_tops_1(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4404,c_40])).

cnf(c_4527,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4526])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2557,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4674,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4527,c_2557])).

cnf(c_8049,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4674,c_35,c_2792,c_2795,c_5221])).

cnf(c_24,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_625,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_626,plain,
    ( ~ v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_2541,plain,
    ( k1_tops_1(sK2,X0) = k1_xboole_0
    | v2_tops_1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_3260,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_2541])).

cnf(c_5292,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5285,c_3260])).

cnf(c_8055,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8049,c_5292])).

cnf(c_8058,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8055,c_2561])).

cnf(c_8062,plain,
    ( r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2564,c_8058])).

cnf(c_2882,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
    | r1_tarski(X0,k4_xboole_0(X2,X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4781,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,sK4))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k4_xboole_0(X1,sK4)) ),
    inference(instantiation,[status(thm)],[c_2882])).

cnf(c_9292,plain,
    ( r1_tarski(sK4,k4_xboole_0(X0,sK4))
    | ~ r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_4781])).

cnf(c_9294,plain,
    ( r1_tarski(sK4,k4_xboole_0(X0,sK4)) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k4_xboole_0(X0,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9292])).

cnf(c_6611,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9293,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_6611])).

cnf(c_9298,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9293])).

cnf(c_6142,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_13028,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6142])).

cnf(c_13033,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13028])).

cnf(c_13097,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12665,c_35,c_42,c_2792,c_2795,c_3663,c_5221,c_8062,c_9294,c_9298,c_13033])).

cnf(c_13104,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2561,c_13097])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:50:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.65/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.98  
% 3.65/0.98  ------  iProver source info
% 3.65/0.98  
% 3.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.98  git: non_committed_changes: false
% 3.65/0.98  git: last_make_outside_of_git: false
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  
% 3.65/0.98  ------ Input Options
% 3.65/0.98  
% 3.65/0.98  --out_options                           all
% 3.65/0.98  --tptp_safe_out                         true
% 3.65/0.98  --problem_path                          ""
% 3.65/0.98  --include_path                          ""
% 3.65/0.98  --clausifier                            res/vclausify_rel
% 3.65/0.98  --clausifier_options                    --mode clausify
% 3.65/0.98  --stdin                                 false
% 3.65/0.98  --stats_out                             all
% 3.65/0.98  
% 3.65/0.98  ------ General Options
% 3.65/0.98  
% 3.65/0.98  --fof                                   false
% 3.65/0.98  --time_out_real                         305.
% 3.65/0.98  --time_out_virtual                      -1.
% 3.65/0.98  --symbol_type_check                     false
% 3.65/0.98  --clausify_out                          false
% 3.65/0.98  --sig_cnt_out                           false
% 3.65/0.98  --trig_cnt_out                          false
% 3.65/0.98  --trig_cnt_out_tolerance                1.
% 3.65/0.98  --trig_cnt_out_sk_spl                   false
% 3.65/0.98  --abstr_cl_out                          false
% 3.65/0.98  
% 3.65/0.98  ------ Global Options
% 3.65/0.98  
% 3.65/0.98  --schedule                              default
% 3.65/0.98  --add_important_lit                     false
% 3.65/0.98  --prop_solver_per_cl                    1000
% 3.65/0.98  --min_unsat_core                        false
% 3.65/0.98  --soft_assumptions                      false
% 3.65/0.98  --soft_lemma_size                       3
% 3.65/0.98  --prop_impl_unit_size                   0
% 3.65/0.98  --prop_impl_unit                        []
% 3.65/0.98  --share_sel_clauses                     true
% 3.65/0.98  --reset_solvers                         false
% 3.65/0.98  --bc_imp_inh                            [conj_cone]
% 3.65/0.98  --conj_cone_tolerance                   3.
% 3.65/0.98  --extra_neg_conj                        none
% 3.65/0.98  --large_theory_mode                     true
% 3.65/0.98  --prolific_symb_bound                   200
% 3.65/0.98  --lt_threshold                          2000
% 3.65/0.98  --clause_weak_htbl                      true
% 3.65/0.98  --gc_record_bc_elim                     false
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing Options
% 3.65/0.98  
% 3.65/0.98  --preprocessing_flag                    true
% 3.65/0.98  --time_out_prep_mult                    0.1
% 3.65/0.98  --splitting_mode                        input
% 3.65/0.98  --splitting_grd                         true
% 3.65/0.98  --splitting_cvd                         false
% 3.65/0.98  --splitting_cvd_svl                     false
% 3.65/0.98  --splitting_nvd                         32
% 3.65/0.98  --sub_typing                            true
% 3.65/0.98  --prep_gs_sim                           true
% 3.65/0.98  --prep_unflatten                        true
% 3.65/0.98  --prep_res_sim                          true
% 3.65/0.98  --prep_upred                            true
% 3.65/0.98  --prep_sem_filter                       exhaustive
% 3.65/0.98  --prep_sem_filter_out                   false
% 3.65/0.98  --pred_elim                             true
% 3.65/0.98  --res_sim_input                         true
% 3.65/0.98  --eq_ax_congr_red                       true
% 3.65/0.98  --pure_diseq_elim                       true
% 3.65/0.98  --brand_transform                       false
% 3.65/0.98  --non_eq_to_eq                          false
% 3.65/0.98  --prep_def_merge                        true
% 3.65/0.98  --prep_def_merge_prop_impl              false
% 3.65/0.98  --prep_def_merge_mbd                    true
% 3.65/0.98  --prep_def_merge_tr_red                 false
% 3.65/0.98  --prep_def_merge_tr_cl                  false
% 3.65/0.98  --smt_preprocessing                     true
% 3.65/0.98  --smt_ac_axioms                         fast
% 3.65/0.98  --preprocessed_out                      false
% 3.65/0.98  --preprocessed_stats                    false
% 3.65/0.98  
% 3.65/0.98  ------ Abstraction refinement Options
% 3.65/0.98  
% 3.65/0.98  --abstr_ref                             []
% 3.65/0.98  --abstr_ref_prep                        false
% 3.65/0.98  --abstr_ref_until_sat                   false
% 3.65/0.98  --abstr_ref_sig_restrict                funpre
% 3.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.98  --abstr_ref_under                       []
% 3.65/0.98  
% 3.65/0.98  ------ SAT Options
% 3.65/0.98  
% 3.65/0.98  --sat_mode                              false
% 3.65/0.98  --sat_fm_restart_options                ""
% 3.65/0.98  --sat_gr_def                            false
% 3.65/0.98  --sat_epr_types                         true
% 3.65/0.98  --sat_non_cyclic_types                  false
% 3.65/0.98  --sat_finite_models                     false
% 3.65/0.98  --sat_fm_lemmas                         false
% 3.65/0.98  --sat_fm_prep                           false
% 3.65/0.98  --sat_fm_uc_incr                        true
% 3.65/0.98  --sat_out_model                         small
% 3.65/0.98  --sat_out_clauses                       false
% 3.65/0.98  
% 3.65/0.98  ------ QBF Options
% 3.65/0.98  
% 3.65/0.98  --qbf_mode                              false
% 3.65/0.98  --qbf_elim_univ                         false
% 3.65/0.98  --qbf_dom_inst                          none
% 3.65/0.98  --qbf_dom_pre_inst                      false
% 3.65/0.98  --qbf_sk_in                             false
% 3.65/0.98  --qbf_pred_elim                         true
% 3.65/0.98  --qbf_split                             512
% 3.65/0.98  
% 3.65/0.98  ------ BMC1 Options
% 3.65/0.98  
% 3.65/0.98  --bmc1_incremental                      false
% 3.65/0.98  --bmc1_axioms                           reachable_all
% 3.65/0.98  --bmc1_min_bound                        0
% 3.65/0.98  --bmc1_max_bound                        -1
% 3.65/0.98  --bmc1_max_bound_default                -1
% 3.65/0.98  --bmc1_symbol_reachability              true
% 3.65/0.98  --bmc1_property_lemmas                  false
% 3.65/0.98  --bmc1_k_induction                      false
% 3.65/0.98  --bmc1_non_equiv_states                 false
% 3.65/0.98  --bmc1_deadlock                         false
% 3.65/0.98  --bmc1_ucm                              false
% 3.65/0.98  --bmc1_add_unsat_core                   none
% 3.65/0.98  --bmc1_unsat_core_children              false
% 3.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.98  --bmc1_out_stat                         full
% 3.65/0.98  --bmc1_ground_init                      false
% 3.65/0.98  --bmc1_pre_inst_next_state              false
% 3.65/0.98  --bmc1_pre_inst_state                   false
% 3.65/0.98  --bmc1_pre_inst_reach_state             false
% 3.65/0.98  --bmc1_out_unsat_core                   false
% 3.65/0.98  --bmc1_aig_witness_out                  false
% 3.65/0.98  --bmc1_verbose                          false
% 3.65/0.98  --bmc1_dump_clauses_tptp                false
% 3.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.98  --bmc1_dump_file                        -
% 3.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.98  --bmc1_ucm_extend_mode                  1
% 3.65/0.98  --bmc1_ucm_init_mode                    2
% 3.65/0.98  --bmc1_ucm_cone_mode                    none
% 3.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.98  --bmc1_ucm_relax_model                  4
% 3.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.98  --bmc1_ucm_layered_model                none
% 3.65/0.98  --bmc1_ucm_max_lemma_size               10
% 3.65/0.98  
% 3.65/0.98  ------ AIG Options
% 3.65/0.98  
% 3.65/0.98  --aig_mode                              false
% 3.65/0.98  
% 3.65/0.98  ------ Instantiation Options
% 3.65/0.98  
% 3.65/0.98  --instantiation_flag                    true
% 3.65/0.98  --inst_sos_flag                         false
% 3.65/0.98  --inst_sos_phase                        true
% 3.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel_side                     num_symb
% 3.65/0.98  --inst_solver_per_active                1400
% 3.65/0.98  --inst_solver_calls_frac                1.
% 3.65/0.98  --inst_passive_queue_type               priority_queues
% 3.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.98  --inst_passive_queues_freq              [25;2]
% 3.65/0.98  --inst_dismatching                      true
% 3.65/0.98  --inst_eager_unprocessed_to_passive     true
% 3.65/0.98  --inst_prop_sim_given                   true
% 3.65/0.98  --inst_prop_sim_new                     false
% 3.65/0.98  --inst_subs_new                         false
% 3.65/0.98  --inst_eq_res_simp                      false
% 3.65/0.98  --inst_subs_given                       false
% 3.65/0.98  --inst_orphan_elimination               true
% 3.65/0.98  --inst_learning_loop_flag               true
% 3.65/0.98  --inst_learning_start                   3000
% 3.65/0.98  --inst_learning_factor                  2
% 3.65/0.98  --inst_start_prop_sim_after_learn       3
% 3.65/0.98  --inst_sel_renew                        solver
% 3.65/0.98  --inst_lit_activity_flag                true
% 3.65/0.98  --inst_restr_to_given                   false
% 3.65/0.98  --inst_activity_threshold               500
% 3.65/0.98  --inst_out_proof                        true
% 3.65/0.98  
% 3.65/0.98  ------ Resolution Options
% 3.65/0.98  
% 3.65/0.98  --resolution_flag                       true
% 3.65/0.98  --res_lit_sel                           adaptive
% 3.65/0.98  --res_lit_sel_side                      none
% 3.65/0.98  --res_ordering                          kbo
% 3.65/0.98  --res_to_prop_solver                    active
% 3.65/0.98  --res_prop_simpl_new                    false
% 3.65/0.98  --res_prop_simpl_given                  true
% 3.65/0.98  --res_passive_queue_type                priority_queues
% 3.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.98  --res_passive_queues_freq               [15;5]
% 3.65/0.98  --res_forward_subs                      full
% 3.65/0.98  --res_backward_subs                     full
% 3.65/0.98  --res_forward_subs_resolution           true
% 3.65/0.98  --res_backward_subs_resolution          true
% 3.65/0.98  --res_orphan_elimination                true
% 3.65/0.98  --res_time_limit                        2.
% 3.65/0.98  --res_out_proof                         true
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Options
% 3.65/0.98  
% 3.65/0.98  --superposition_flag                    true
% 3.65/0.98  --sup_passive_queue_type                priority_queues
% 3.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.98  --demod_completeness_check              fast
% 3.65/0.98  --demod_use_ground                      true
% 3.65/0.98  --sup_to_prop_solver                    passive
% 3.65/0.98  --sup_prop_simpl_new                    true
% 3.65/0.98  --sup_prop_simpl_given                  true
% 3.65/0.98  --sup_fun_splitting                     false
% 3.65/0.98  --sup_smt_interval                      50000
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Simplification Setup
% 3.65/0.98  
% 3.65/0.98  --sup_indices_passive                   []
% 3.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_full_bw                           [BwDemod]
% 3.65/0.98  --sup_immed_triv                        [TrivRules]
% 3.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_immed_bw_main                     []
% 3.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  
% 3.65/0.98  ------ Combination Options
% 3.65/0.98  
% 3.65/0.98  --comb_res_mult                         3
% 3.65/0.98  --comb_sup_mult                         2
% 3.65/0.98  --comb_inst_mult                        10
% 3.65/0.98  
% 3.65/0.98  ------ Debug Options
% 3.65/0.98  
% 3.65/0.98  --dbg_backtrace                         false
% 3.65/0.98  --dbg_dump_prop_clauses                 false
% 3.65/0.98  --dbg_dump_prop_clauses_file            -
% 3.65/0.98  --dbg_out_stat                          false
% 3.65/0.98  ------ Parsing...
% 3.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.98  ------ Proving...
% 3.65/0.98  ------ Problem Properties 
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  clauses                                 35
% 3.65/0.98  conjectures                             6
% 3.65/0.98  EPR                                     9
% 3.65/0.98  Horn                                    31
% 3.65/0.98  unary                                   7
% 3.65/0.98  binary                                  16
% 3.65/0.98  lits                                    82
% 3.65/0.98  lits eq                                 12
% 3.65/0.98  fd_pure                                 0
% 3.65/0.98  fd_pseudo                               0
% 3.65/0.98  fd_cond                                 2
% 3.65/0.98  fd_pseudo_cond                          0
% 3.65/0.98  AC symbols                              0
% 3.65/0.98  
% 3.65/0.98  ------ Schedule dynamic 5 is on 
% 3.65/0.98  
% 3.65/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  Current options:
% 3.65/0.98  ------ 
% 3.65/0.98  
% 3.65/0.98  ------ Input Options
% 3.65/0.98  
% 3.65/0.98  --out_options                           all
% 3.65/0.98  --tptp_safe_out                         true
% 3.65/0.98  --problem_path                          ""
% 3.65/0.98  --include_path                          ""
% 3.65/0.98  --clausifier                            res/vclausify_rel
% 3.65/0.98  --clausifier_options                    --mode clausify
% 3.65/0.98  --stdin                                 false
% 3.65/0.98  --stats_out                             all
% 3.65/0.98  
% 3.65/0.98  ------ General Options
% 3.65/0.98  
% 3.65/0.98  --fof                                   false
% 3.65/0.98  --time_out_real                         305.
% 3.65/0.98  --time_out_virtual                      -1.
% 3.65/0.98  --symbol_type_check                     false
% 3.65/0.98  --clausify_out                          false
% 3.65/0.98  --sig_cnt_out                           false
% 3.65/0.98  --trig_cnt_out                          false
% 3.65/0.98  --trig_cnt_out_tolerance                1.
% 3.65/0.98  --trig_cnt_out_sk_spl                   false
% 3.65/0.98  --abstr_cl_out                          false
% 3.65/0.98  
% 3.65/0.98  ------ Global Options
% 3.65/0.98  
% 3.65/0.98  --schedule                              default
% 3.65/0.98  --add_important_lit                     false
% 3.65/0.98  --prop_solver_per_cl                    1000
% 3.65/0.98  --min_unsat_core                        false
% 3.65/0.98  --soft_assumptions                      false
% 3.65/0.98  --soft_lemma_size                       3
% 3.65/0.98  --prop_impl_unit_size                   0
% 3.65/0.98  --prop_impl_unit                        []
% 3.65/0.98  --share_sel_clauses                     true
% 3.65/0.98  --reset_solvers                         false
% 3.65/0.98  --bc_imp_inh                            [conj_cone]
% 3.65/0.98  --conj_cone_tolerance                   3.
% 3.65/0.98  --extra_neg_conj                        none
% 3.65/0.98  --large_theory_mode                     true
% 3.65/0.98  --prolific_symb_bound                   200
% 3.65/0.98  --lt_threshold                          2000
% 3.65/0.98  --clause_weak_htbl                      true
% 3.65/0.98  --gc_record_bc_elim                     false
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing Options
% 3.65/0.98  
% 3.65/0.98  --preprocessing_flag                    true
% 3.65/0.98  --time_out_prep_mult                    0.1
% 3.65/0.98  --splitting_mode                        input
% 3.65/0.98  --splitting_grd                         true
% 3.65/0.98  --splitting_cvd                         false
% 3.65/0.98  --splitting_cvd_svl                     false
% 3.65/0.98  --splitting_nvd                         32
% 3.65/0.98  --sub_typing                            true
% 3.65/0.98  --prep_gs_sim                           true
% 3.65/0.98  --prep_unflatten                        true
% 3.65/0.98  --prep_res_sim                          true
% 3.65/0.98  --prep_upred                            true
% 3.65/0.98  --prep_sem_filter                       exhaustive
% 3.65/0.98  --prep_sem_filter_out                   false
% 3.65/0.98  --pred_elim                             true
% 3.65/0.98  --res_sim_input                         true
% 3.65/0.98  --eq_ax_congr_red                       true
% 3.65/0.98  --pure_diseq_elim                       true
% 3.65/0.98  --brand_transform                       false
% 3.65/0.98  --non_eq_to_eq                          false
% 3.65/0.98  --prep_def_merge                        true
% 3.65/0.98  --prep_def_merge_prop_impl              false
% 3.65/0.98  --prep_def_merge_mbd                    true
% 3.65/0.98  --prep_def_merge_tr_red                 false
% 3.65/0.98  --prep_def_merge_tr_cl                  false
% 3.65/0.98  --smt_preprocessing                     true
% 3.65/0.98  --smt_ac_axioms                         fast
% 3.65/0.98  --preprocessed_out                      false
% 3.65/0.98  --preprocessed_stats                    false
% 3.65/0.98  
% 3.65/0.98  ------ Abstraction refinement Options
% 3.65/0.98  
% 3.65/0.98  --abstr_ref                             []
% 3.65/0.98  --abstr_ref_prep                        false
% 3.65/0.98  --abstr_ref_until_sat                   false
% 3.65/0.98  --abstr_ref_sig_restrict                funpre
% 3.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.98  --abstr_ref_under                       []
% 3.65/0.98  
% 3.65/0.98  ------ SAT Options
% 3.65/0.98  
% 3.65/0.98  --sat_mode                              false
% 3.65/0.98  --sat_fm_restart_options                ""
% 3.65/0.98  --sat_gr_def                            false
% 3.65/0.98  --sat_epr_types                         true
% 3.65/0.98  --sat_non_cyclic_types                  false
% 3.65/0.98  --sat_finite_models                     false
% 3.65/0.98  --sat_fm_lemmas                         false
% 3.65/0.98  --sat_fm_prep                           false
% 3.65/0.98  --sat_fm_uc_incr                        true
% 3.65/0.98  --sat_out_model                         small
% 3.65/0.98  --sat_out_clauses                       false
% 3.65/0.98  
% 3.65/0.98  ------ QBF Options
% 3.65/0.98  
% 3.65/0.98  --qbf_mode                              false
% 3.65/0.98  --qbf_elim_univ                         false
% 3.65/0.98  --qbf_dom_inst                          none
% 3.65/0.98  --qbf_dom_pre_inst                      false
% 3.65/0.98  --qbf_sk_in                             false
% 3.65/0.98  --qbf_pred_elim                         true
% 3.65/0.98  --qbf_split                             512
% 3.65/0.98  
% 3.65/0.98  ------ BMC1 Options
% 3.65/0.98  
% 3.65/0.98  --bmc1_incremental                      false
% 3.65/0.98  --bmc1_axioms                           reachable_all
% 3.65/0.98  --bmc1_min_bound                        0
% 3.65/0.98  --bmc1_max_bound                        -1
% 3.65/0.98  --bmc1_max_bound_default                -1
% 3.65/0.98  --bmc1_symbol_reachability              true
% 3.65/0.98  --bmc1_property_lemmas                  false
% 3.65/0.98  --bmc1_k_induction                      false
% 3.65/0.98  --bmc1_non_equiv_states                 false
% 3.65/0.98  --bmc1_deadlock                         false
% 3.65/0.98  --bmc1_ucm                              false
% 3.65/0.98  --bmc1_add_unsat_core                   none
% 3.65/0.98  --bmc1_unsat_core_children              false
% 3.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.98  --bmc1_out_stat                         full
% 3.65/0.98  --bmc1_ground_init                      false
% 3.65/0.98  --bmc1_pre_inst_next_state              false
% 3.65/0.98  --bmc1_pre_inst_state                   false
% 3.65/0.98  --bmc1_pre_inst_reach_state             false
% 3.65/0.98  --bmc1_out_unsat_core                   false
% 3.65/0.98  --bmc1_aig_witness_out                  false
% 3.65/0.98  --bmc1_verbose                          false
% 3.65/0.98  --bmc1_dump_clauses_tptp                false
% 3.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.98  --bmc1_dump_file                        -
% 3.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.98  --bmc1_ucm_extend_mode                  1
% 3.65/0.98  --bmc1_ucm_init_mode                    2
% 3.65/0.98  --bmc1_ucm_cone_mode                    none
% 3.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.98  --bmc1_ucm_relax_model                  4
% 3.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.98  --bmc1_ucm_layered_model                none
% 3.65/0.98  --bmc1_ucm_max_lemma_size               10
% 3.65/0.98  
% 3.65/0.98  ------ AIG Options
% 3.65/0.98  
% 3.65/0.98  --aig_mode                              false
% 3.65/0.98  
% 3.65/0.98  ------ Instantiation Options
% 3.65/0.98  
% 3.65/0.98  --instantiation_flag                    true
% 3.65/0.98  --inst_sos_flag                         false
% 3.65/0.98  --inst_sos_phase                        true
% 3.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel_side                     none
% 3.65/0.98  --inst_solver_per_active                1400
% 3.65/0.98  --inst_solver_calls_frac                1.
% 3.65/0.98  --inst_passive_queue_type               priority_queues
% 3.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.98  --inst_passive_queues_freq              [25;2]
% 3.65/0.98  --inst_dismatching                      true
% 3.65/0.98  --inst_eager_unprocessed_to_passive     true
% 3.65/0.98  --inst_prop_sim_given                   true
% 3.65/0.98  --inst_prop_sim_new                     false
% 3.65/0.98  --inst_subs_new                         false
% 3.65/0.98  --inst_eq_res_simp                      false
% 3.65/0.98  --inst_subs_given                       false
% 3.65/0.98  --inst_orphan_elimination               true
% 3.65/0.98  --inst_learning_loop_flag               true
% 3.65/0.98  --inst_learning_start                   3000
% 3.65/0.98  --inst_learning_factor                  2
% 3.65/0.98  --inst_start_prop_sim_after_learn       3
% 3.65/0.98  --inst_sel_renew                        solver
% 3.65/0.98  --inst_lit_activity_flag                true
% 3.65/0.98  --inst_restr_to_given                   false
% 3.65/0.98  --inst_activity_threshold               500
% 3.65/0.98  --inst_out_proof                        true
% 3.65/0.98  
% 3.65/0.98  ------ Resolution Options
% 3.65/0.98  
% 3.65/0.98  --resolution_flag                       false
% 3.65/0.98  --res_lit_sel                           adaptive
% 3.65/0.98  --res_lit_sel_side                      none
% 3.65/0.98  --res_ordering                          kbo
% 3.65/0.98  --res_to_prop_solver                    active
% 3.65/0.98  --res_prop_simpl_new                    false
% 3.65/0.98  --res_prop_simpl_given                  true
% 3.65/0.98  --res_passive_queue_type                priority_queues
% 3.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.98  --res_passive_queues_freq               [15;5]
% 3.65/0.98  --res_forward_subs                      full
% 3.65/0.98  --res_backward_subs                     full
% 3.65/0.98  --res_forward_subs_resolution           true
% 3.65/0.98  --res_backward_subs_resolution          true
% 3.65/0.98  --res_orphan_elimination                true
% 3.65/0.98  --res_time_limit                        2.
% 3.65/0.98  --res_out_proof                         true
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Options
% 3.65/0.98  
% 3.65/0.98  --superposition_flag                    true
% 3.65/0.98  --sup_passive_queue_type                priority_queues
% 3.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.98  --demod_completeness_check              fast
% 3.65/0.98  --demod_use_ground                      true
% 3.65/0.98  --sup_to_prop_solver                    passive
% 3.65/0.98  --sup_prop_simpl_new                    true
% 3.65/0.98  --sup_prop_simpl_given                  true
% 3.65/0.98  --sup_fun_splitting                     false
% 3.65/0.98  --sup_smt_interval                      50000
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Simplification Setup
% 3.65/0.98  
% 3.65/0.98  --sup_indices_passive                   []
% 3.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_full_bw                           [BwDemod]
% 3.65/0.98  --sup_immed_triv                        [TrivRules]
% 3.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_immed_bw_main                     []
% 3.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  
% 3.65/0.98  ------ Combination Options
% 3.65/0.98  
% 3.65/0.98  --comb_res_mult                         3
% 3.65/0.98  --comb_sup_mult                         2
% 3.65/0.98  --comb_inst_mult                        10
% 3.65/0.98  
% 3.65/0.98  ------ Debug Options
% 3.65/0.98  
% 3.65/0.98  --dbg_backtrace                         false
% 3.65/0.98  --dbg_dump_prop_clauses                 false
% 3.65/0.98  --dbg_dump_prop_clauses_file            -
% 3.65/0.98  --dbg_out_stat                          false
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ Proving...
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS status Theorem for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98   Resolution empty clause
% 3.65/0.98  
% 3.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  fof(f6,axiom,(
% 3.65/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f59,plain,(
% 3.65/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f6])).
% 3.65/0.98  
% 3.65/0.98  fof(f1,axiom,(
% 3.65/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f52,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f1])).
% 3.65/0.98  
% 3.65/0.98  fof(f10,axiom,(
% 3.65/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f63,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f10])).
% 3.65/0.98  
% 3.65/0.98  fof(f87,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.65/0.98    inference(definition_unfolding,[],[f52,f63,f63])).
% 3.65/0.98  
% 3.65/0.98  fof(f9,axiom,(
% 3.65/0.98    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f62,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.65/0.98    inference(cnf_transformation,[],[f9])).
% 3.65/0.98  
% 3.65/0.98  fof(f3,axiom,(
% 3.65/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f56,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f3])).
% 3.65/0.98  
% 3.65/0.98  fof(f86,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.65/0.98    inference(definition_unfolding,[],[f56,f63])).
% 3.65/0.98  
% 3.65/0.98  fof(f8,axiom,(
% 3.65/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f61,plain,(
% 3.65/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.65/0.98    inference(cnf_transformation,[],[f8])).
% 3.65/0.98  
% 3.65/0.98  fof(f7,axiom,(
% 3.65/0.98    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f23,plain,(
% 3.65/0.98    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f7])).
% 3.65/0.98  
% 3.65/0.98  fof(f60,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f23])).
% 3.65/0.98  
% 3.65/0.98  fof(f5,axiom,(
% 3.65/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f58,plain,(
% 3.65/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.65/0.98    inference(cnf_transformation,[],[f5])).
% 3.65/0.98  
% 3.65/0.98  fof(f88,plain,(
% 3.65/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.65/0.98    inference(definition_unfolding,[],[f58,f63])).
% 3.65/0.98  
% 3.65/0.98  fof(f18,conjecture,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f19,negated_conjecture,(
% 3.65/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 3.65/0.98    inference(negated_conjecture,[],[f18])).
% 3.65/0.98  
% 3.65/0.98  fof(f33,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f19])).
% 3.65/0.98  
% 3.65/0.98  fof(f34,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f33])).
% 3.65/0.98  
% 3.65/0.98  fof(f45,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f34])).
% 3.65/0.98  
% 3.65/0.98  fof(f46,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f45])).
% 3.65/0.98  
% 3.65/0.98  fof(f47,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.65/0.98    inference(rectify,[],[f46])).
% 3.65/0.98  
% 3.65/0.98  fof(f50,plain,(
% 3.65/0.98    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK4 & v3_pre_topc(sK4,X0) & r1_tarski(sK4,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f49,plain,(
% 3.65/0.98    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK3,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f48,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(X1,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f51,plain,(
% 3.65/0.98    (((k1_xboole_0 != sK4 & v3_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(sK3,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f50,f49,f48])).
% 3.65/0.98  
% 3.65/0.98  fof(f85,plain,(
% 3.65/0.98    k1_xboole_0 != sK4 | ~v2_tops_1(sK3,sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f15,axiom,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f28,plain,(
% 3.65/0.98    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f15])).
% 3.65/0.98  
% 3.65/0.98  fof(f29,plain,(
% 3.65/0.98    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f28])).
% 3.65/0.98  
% 3.65/0.98  fof(f40,plain,(
% 3.65/0.98    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f29])).
% 3.65/0.98  
% 3.65/0.98  fof(f41,plain,(
% 3.65/0.98    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.65/0.98    inference(rectify,[],[f40])).
% 3.65/0.98  
% 3.65/0.98  fof(f42,plain,(
% 3.65/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f43,plain,(
% 3.65/0.98    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.65/0.98  
% 3.65/0.98  fof(f69,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f43])).
% 3.65/0.98  
% 3.65/0.98  fof(f78,plain,(
% 3.65/0.98    v2_pre_topc(sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f79,plain,(
% 3.65/0.98    l1_pre_topc(sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f81,plain,(
% 3.65/0.98    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f80,plain,(
% 3.65/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f17,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f32,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f17])).
% 3.65/0.98  
% 3.65/0.98  fof(f44,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f32])).
% 3.65/0.98  
% 3.65/0.98  fof(f77,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f44])).
% 3.65/0.98  
% 3.65/0.98  fof(f14,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f27,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f14])).
% 3.65/0.98  
% 3.65/0.98  fof(f68,plain,(
% 3.65/0.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f27])).
% 3.65/0.98  
% 3.65/0.98  fof(f13,axiom,(
% 3.65/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f25,plain,(
% 3.65/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f13])).
% 3.65/0.98  
% 3.65/0.98  fof(f26,plain,(
% 3.65/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f25])).
% 3.65/0.98  
% 3.65/0.98  fof(f67,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f26])).
% 3.65/0.98  
% 3.65/0.98  fof(f11,axiom,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f39,plain,(
% 3.65/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.65/0.98    inference(nnf_transformation,[],[f11])).
% 3.65/0.98  
% 3.65/0.98  fof(f65,plain,(
% 3.65/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f39])).
% 3.65/0.98  
% 3.65/0.98  fof(f64,plain,(
% 3.65/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f39])).
% 3.65/0.98  
% 3.65/0.98  fof(f4,axiom,(
% 3.65/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f21,plain,(
% 3.65/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.65/0.98    inference(ennf_transformation,[],[f4])).
% 3.65/0.98  
% 3.65/0.98  fof(f22,plain,(
% 3.65/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.65/0.98    inference(flattening,[],[f21])).
% 3.65/0.98  
% 3.65/0.98  fof(f57,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f22])).
% 3.65/0.98  
% 3.65/0.98  fof(f2,axiom,(
% 3.65/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f20,plain,(
% 3.65/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f2])).
% 3.65/0.98  
% 3.65/0.98  fof(f35,plain,(
% 3.65/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.65/0.98    inference(nnf_transformation,[],[f20])).
% 3.65/0.98  
% 3.65/0.98  fof(f36,plain,(
% 3.65/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.65/0.98    inference(rectify,[],[f35])).
% 3.65/0.98  
% 3.65/0.98  fof(f37,plain,(
% 3.65/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f38,plain,(
% 3.65/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.65/0.98  
% 3.65/0.98  fof(f54,plain,(
% 3.65/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f38])).
% 3.65/0.98  
% 3.65/0.98  fof(f82,plain,(
% 3.65/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tops_1(sK3,sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f73,plain,(
% 3.65/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f43])).
% 3.65/0.98  
% 3.65/0.98  fof(f84,plain,(
% 3.65/0.98    v3_pre_topc(sK4,sK2) | ~v2_tops_1(sK3,sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f83,plain,(
% 3.65/0.98    r1_tarski(sK4,sK3) | ~v2_tops_1(sK3,sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f12,axiom,(
% 3.65/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f24,plain,(
% 3.65/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.65/0.98    inference(ennf_transformation,[],[f12])).
% 3.65/0.98  
% 3.65/0.98  fof(f66,plain,(
% 3.65/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f24])).
% 3.65/0.98  
% 3.65/0.98  fof(f76,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f44])).
% 3.65/0.98  
% 3.65/0.98  cnf(c_7,plain,
% 3.65/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2561,plain,
% 3.65/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1,plain,
% 3.65/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.65/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_10,plain,
% 3.65/0.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_0,plain,
% 3.65/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3129,plain,
% 3.65/0.98      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4120,plain,
% 3.65/0.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_3129]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5732,plain,
% 3.65/0.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_4120]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9373,plain,
% 3.65/0.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_5732]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_10219,plain,
% 3.65/0.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_9373]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11054,plain,
% 3.65/0.98      ( k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k2_xboole_0(X0,X1)) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_10,c_10219]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9,plain,
% 3.65/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11066,plain,
% 3.65/0.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k2_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0))) ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_11054,c_9]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11067,plain,
% 3.65/0.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_11066,c_10,c_3129]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11108,plain,
% 3.65/0.98      ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0))) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_11067,c_3129]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11119,plain,
% 3.65/0.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0))) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_11108,c_0,c_9]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2560,plain,
% 3.65/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4180,plain,
% 3.65/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.65/0.98      | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_2560]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6539,plain,
% 3.65/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.65/0.98      | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_4180]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6793,plain,
% 3.65/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.65/0.98      | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_6539]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11309,plain,
% 3.65/0.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k2_xboole_0(X0,X1))) = k1_xboole_0
% 3.65/0.98      | r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_11119,c_6793]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11366,plain,
% 3.65/0.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k1_xboole_0) = k1_xboole_0
% 3.65/0.98      | r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)))) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_11309,c_11067]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6,plain,
% 3.65/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2582,plain,
% 3.65/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_6,c_9]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11367,plain,
% 3.65/0.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0
% 3.65/0.98      | r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)),k1_xboole_0) != iProver_top ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_11366,c_9,c_2582]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12657,plain,
% 3.65/0.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0
% 3.65/0.98      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),k1_xboole_0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1,c_11367]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12665,plain,
% 3.65/0.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0
% 3.65/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_12657,c_9,c_10]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_25,negated_conjecture,
% 3.65/0.98      ( ~ v2_tops_1(sK3,sK2) | k1_xboole_0 != sK4 ),
% 3.65/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_42,plain,
% 3.65/0.98      ( k1_xboole_0 != sK4 | v2_tops_1(sK3,sK2) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3662,plain,
% 3.65/0.98      ( ~ r1_tarski(sK4,k4_xboole_0(X0,sK4)) | k1_xboole_0 = sK4 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3663,plain,
% 3.65/0.98      ( k1_xboole_0 = sK4 | r1_tarski(sK4,k4_xboole_0(X0,sK4)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3662]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_20,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_32,negated_conjecture,
% 3.65/0.98      ( v2_pre_topc(sK2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_455,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | sK2 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_456,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.65/0.98      | ~ l1_pre_topc(sK2) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_455]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_31,negated_conjecture,
% 3.65/0.98      ( l1_pre_topc(sK2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_460,plain,
% 3.65/0.98      ( ~ r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.65/0.98      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_456,c_31]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_461,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_460]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2548,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.65/0.98      | r2_hidden(X1,k1_tops_1(sK2,X0)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_29,negated_conjecture,
% 3.65/0.98      ( v2_tops_1(sK3,sK2)
% 3.65/0.98      | ~ v3_pre_topc(X0,sK2)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ r1_tarski(X0,sK3)
% 3.65/0.98      | k1_xboole_0 = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2552,plain,
% 3.65/0.98      ( k1_xboole_0 = X0
% 3.65/0.98      | v2_tops_1(sK3,sK2) = iProver_top
% 3.65/0.98      | v3_pre_topc(X0,sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | r1_tarski(X0,sK3) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3805,plain,
% 3.65/0.98      ( sK1(sK2,X0,X1) = k1_xboole_0
% 3.65/0.98      | v2_tops_1(sK3,sK2) = iProver_top
% 3.65/0.98      | v3_pre_topc(sK1(sK2,X0,X1),sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | r2_hidden(X0,k1_tops_1(sK2,X1)) != iProver_top
% 3.65/0.98      | r1_tarski(sK1(sK2,X0,X1),sK3) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2548,c_2552]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_30,negated_conjecture,
% 3.65/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.65/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_35,plain,
% 3.65/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_23,plain,
% 3.65/0.98      ( v2_tops_1(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_640,plain,
% 3.65/0.98      ( v2_tops_1(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | k1_tops_1(X1,X0) != k1_xboole_0
% 3.65/0.98      | sK2 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_641,plain,
% 3.65/0.98      ( v2_tops_1(X0,sK2)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | k1_tops_1(sK2,X0) != k1_xboole_0 ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_640]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2791,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2)
% 3.65/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_641]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2792,plain,
% 3.65/0.98      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 3.65/0.98      | v2_tops_1(sK3,sK2) = iProver_top
% 3.65/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2791]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_15,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_655,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.65/0.98      | sK2 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_656,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_655]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2794,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_656]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2795,plain,
% 3.65/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2794]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2551,plain,
% 3.65/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_14,plain,
% 3.65/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.65/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/0.98      | ~ v2_pre_topc(X0)
% 3.65/0.98      | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_412,plain,
% 3.65/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.65/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/0.98      | ~ l1_pre_topc(X0)
% 3.65/0.98      | sK2 != X0 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_413,plain,
% 3.65/0.98      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ l1_pre_topc(sK2) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_412]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_417,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
% 3.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_413,c_31]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_418,plain,
% 3.65/0.98      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_417]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2549,plain,
% 3.65/0.98      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2) = iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3197,plain,
% 3.65/0.98      ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2551,c_2549]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2559,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.65/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4831,plain,
% 3.65/0.98      ( k1_xboole_0 = X0
% 3.65/0.98      | v2_tops_1(sK3,sK2) = iProver_top
% 3.65/0.98      | v3_pre_topc(X0,sK2) != iProver_top
% 3.65/0.98      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 3.65/0.98      | r1_tarski(X0,sK3) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2559,c_2552]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3028,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3866,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | r1_tarski(sK3,u1_struct_0(sK2)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_3028]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3867,plain,
% 3.65/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3866]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3041,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,X1)
% 3.65/0.98      | ~ r1_tarski(X1,u1_struct_0(sK2))
% 3.65/0.98      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4742,plain,
% 3.65/0.98      ( r1_tarski(X0,u1_struct_0(sK2))
% 3.65/0.98      | ~ r1_tarski(X0,sK3)
% 3.65/0.98      | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_3041]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4743,plain,
% 3.65/0.98      ( r1_tarski(X0,u1_struct_0(sK2)) = iProver_top
% 3.65/0.98      | r1_tarski(X0,sK3) != iProver_top
% 3.65/0.98      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_4742]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5210,plain,
% 3.65/0.98      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.65/0.98      | v2_tops_1(sK3,sK2) = iProver_top
% 3.65/0.98      | k1_xboole_0 = X0
% 3.65/0.98      | r1_tarski(X0,sK3) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_4831,c_35,c_3867,c_4743]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5211,plain,
% 3.65/0.98      ( k1_xboole_0 = X0
% 3.65/0.98      | v2_tops_1(sK3,sK2) = iProver_top
% 3.65/0.98      | v3_pre_topc(X0,sK2) != iProver_top
% 3.65/0.98      | r1_tarski(X0,sK3) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_5210]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5221,plain,
% 3.65/0.98      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 3.65/0.98      | v2_tops_1(sK3,sK2) = iProver_top
% 3.65/0.98      | r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3197,c_5211]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5285,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) = iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_3805,c_35,c_2792,c_2795,c_5221]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3,plain,
% 3.65/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2564,plain,
% 3.65/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.65/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_28,negated_conjecture,
% 3.65/0.98      ( ~ v2_tops_1(sK3,sK2) | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.65/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2553,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_16,plain,
% 3.65/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ r2_hidden(X3,X0)
% 3.65/0.98      | r2_hidden(X3,k1_tops_1(X1,X2))
% 3.65/0.98      | ~ r1_tarski(X0,X2)
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_518,plain,
% 3.65/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ r2_hidden(X3,X0)
% 3.65/0.98      | r2_hidden(X3,k1_tops_1(X1,X2))
% 3.65/0.98      | ~ r1_tarski(X0,X2)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | sK2 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_519,plain,
% 3.65/0.98      ( ~ v3_pre_topc(X0,sK2)
% 3.65/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ r2_hidden(X2,X0)
% 3.65/0.98      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 3.65/0.98      | ~ r1_tarski(X0,X1)
% 3.65/0.98      | ~ l1_pre_topc(sK2) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_518]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_521,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,X1)
% 3.65/0.98      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 3.65/0.98      | ~ r2_hidden(X2,X0)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ v3_pre_topc(X0,sK2) ),
% 3.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_519,c_31]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_522,plain,
% 3.65/0.98      ( ~ v3_pre_topc(X0,sK2)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ r2_hidden(X2,X0)
% 3.65/0.98      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 3.65/0.98      | ~ r1_tarski(X0,X1) ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_521]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2545,plain,
% 3.65/0.98      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.65/0.98      | r2_hidden(X2,k1_tops_1(sK2,X1)) = iProver_top
% 3.65/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3958,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.65/0.98      | v3_pre_topc(sK4,sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 3.65/0.98      | r2_hidden(X1,sK4) != iProver_top
% 3.65/0.98      | r1_tarski(sK4,X0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2553,c_2545]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_39,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_26,negated_conjecture,
% 3.65/0.98      ( ~ v2_tops_1(sK3,sK2) | v3_pre_topc(sK4,sK2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_969,plain,
% 3.65/0.98      ( ~ v2_tops_1(sK3,sK2)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ r2_hidden(X2,X0)
% 3.65/0.98      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 3.65/0.98      | ~ r1_tarski(X0,X1)
% 3.65/0.98      | sK2 != sK2
% 3.65/0.98      | sK4 != X0 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_522]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_970,plain,
% 3.65/0.98      ( ~ v2_tops_1(sK3,sK2)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.65/0.98      | ~ r2_hidden(X1,sK4)
% 3.65/0.98      | ~ r1_tarski(sK4,X0) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_969]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_971,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 3.65/0.98      | r2_hidden(X1,sK4) != iProver_top
% 3.65/0.98      | r1_tarski(sK4,X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4394,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.65/0.98      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 3.65/0.98      | r2_hidden(X1,sK4) != iProver_top
% 3.65/0.98      | r1_tarski(sK4,X0) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_3958,c_39,c_971]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4404,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.65/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.65/0.98      | r2_hidden(X0,sK4) != iProver_top
% 3.65/0.98      | r1_tarski(sK4,sK3) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2551,c_4394]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_27,negated_conjecture,
% 3.65/0.98      ( ~ v2_tops_1(sK3,sK2) | r1_tarski(sK4,sK3) ),
% 3.65/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_40,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top | r1_tarski(sK4,sK3) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4526,plain,
% 3.65/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 3.65/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.65/0.98      | v2_tops_1(sK3,sK2) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_4404,c_40]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4527,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.65/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.65/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_4526]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13,plain,
% 3.65/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2557,plain,
% 3.65/0.98      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4674,plain,
% 3.65/0.98      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.65/0.98      | r2_hidden(X0,sK4) != iProver_top
% 3.65/0.98      | r1_tarski(k1_tops_1(sK2,sK3),X0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_4527,c_2557]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8049,plain,
% 3.65/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 3.65/0.98      | r1_tarski(k1_tops_1(sK2,sK3),X0) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_4674,c_35,c_2792,c_2795,c_5221]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_24,plain,
% 3.65/0.98      ( ~ v2_tops_1(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_625,plain,
% 3.65/0.98      ( ~ v2_tops_1(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | k1_tops_1(X1,X0) = k1_xboole_0
% 3.65/0.98      | sK2 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_626,plain,
% 3.65/0.98      ( ~ v2_tops_1(X0,sK2)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.65/0.98      | k1_tops_1(sK2,X0) = k1_xboole_0 ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_625]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2541,plain,
% 3.65/0.98      ( k1_tops_1(sK2,X0) = k1_xboole_0
% 3.65/0.98      | v2_tops_1(X0,sK2) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3260,plain,
% 3.65/0.98      ( k1_tops_1(sK2,sK3) = k1_xboole_0 | v2_tops_1(sK3,sK2) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2551,c_2541]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5292,plain,
% 3.65/0.98      ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_5285,c_3260]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8055,plain,
% 3.65/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 3.65/0.98      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_8049,c_5292]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8058,plain,
% 3.65/0.98      ( r2_hidden(X0,sK4) != iProver_top ),
% 3.65/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_8055,c_2561]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8062,plain,
% 3.65/0.98      ( r1_tarski(sK4,X0) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2564,c_8058]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2882,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,X1)
% 3.65/0.98      | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
% 3.65/0.98      | r1_tarski(X0,k4_xboole_0(X2,X0)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4781,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,k4_xboole_0(X1,sK4))
% 3.65/0.98      | ~ r1_tarski(sK4,X0)
% 3.65/0.98      | r1_tarski(sK4,k4_xboole_0(X1,sK4)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_2882]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9292,plain,
% 3.65/0.98      ( r1_tarski(sK4,k4_xboole_0(X0,sK4))
% 3.65/0.98      | ~ r1_tarski(sK4,k1_xboole_0)
% 3.65/0.98      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(X0,sK4)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_4781]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9294,plain,
% 3.65/0.98      ( r1_tarski(sK4,k4_xboole_0(X0,sK4)) = iProver_top
% 3.65/0.98      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.65/0.98      | r1_tarski(k1_xboole_0,k4_xboole_0(X0,sK4)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_9292]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6611,plain,
% 3.65/0.98      ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9293,plain,
% 3.65/0.98      ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,sK4)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_6611]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9298,plain,
% 3.65/0.98      ( r1_tarski(k1_xboole_0,k4_xboole_0(X0,sK4)) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_9293]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6142,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13028,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.65/0.98      | ~ r1_tarski(sK4,X0)
% 3.65/0.98      | r1_tarski(sK4,k1_xboole_0) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_6142]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13033,plain,
% 3.65/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.65/0.98      | r1_tarski(sK4,X0) != iProver_top
% 3.65/0.98      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13028]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13097,plain,
% 3.65/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_12665,c_35,c_42,c_2792,c_2795,c_3663,c_5221,c_8062,c_9294,
% 3.65/0.98                 c_9298,c_13033]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13104,plain,
% 3.65/0.98      ( $false ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2561,c_13097]) ).
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  ------                               Statistics
% 3.65/0.98  
% 3.65/0.98  ------ General
% 3.65/0.98  
% 3.65/0.98  abstr_ref_over_cycles:                  0
% 3.65/0.98  abstr_ref_under_cycles:                 0
% 3.65/0.98  gc_basic_clause_elim:                   0
% 3.65/0.98  forced_gc_time:                         0
% 3.65/0.98  parsing_time:                           0.014
% 3.65/0.98  unif_index_cands_time:                  0.
% 3.65/0.98  unif_index_add_time:                    0.
% 3.65/0.98  orderings_time:                         0.
% 3.65/0.98  out_proof_time:                         0.013
% 3.65/0.98  total_time:                             0.337
% 3.65/0.98  num_of_symbols:                         53
% 3.65/0.98  num_of_terms:                           9844
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing
% 3.65/0.98  
% 3.65/0.98  num_of_splits:                          4
% 3.65/0.98  num_of_split_atoms:                     3
% 3.65/0.98  num_of_reused_defs:                     1
% 3.65/0.98  num_eq_ax_congr_red:                    29
% 3.65/0.98  num_of_sem_filtered_clauses:            4
% 3.65/0.98  num_of_subtypes:                        0
% 3.65/0.98  monotx_restored_types:                  0
% 3.65/0.98  sat_num_of_epr_types:                   0
% 3.65/0.98  sat_num_of_non_cyclic_types:            0
% 3.65/0.98  sat_guarded_non_collapsed_types:        0
% 3.65/0.98  num_pure_diseq_elim:                    0
% 3.65/0.98  simp_replaced_by:                       0
% 3.65/0.98  res_preprocessed:                       156
% 3.65/0.98  prep_upred:                             0
% 3.65/0.98  prep_unflattend:                        41
% 3.65/0.98  smt_new_axioms:                         0
% 3.65/0.98  pred_elim_cands:                        5
% 3.65/0.98  pred_elim:                              2
% 3.65/0.98  pred_elim_cl:                           2
% 3.65/0.98  pred_elim_cycles:                       6
% 3.65/0.98  merged_defs:                            8
% 3.65/0.98  merged_defs_ncl:                        0
% 3.65/0.98  bin_hyper_res:                          8
% 3.65/0.98  prep_cycles:                            4
% 3.65/0.98  pred_elim_time:                         0.025
% 3.65/0.98  splitting_time:                         0.
% 3.65/0.98  sem_filter_time:                        0.
% 3.65/0.98  monotx_time:                            0.
% 3.65/0.98  subtype_inf_time:                       0.
% 3.65/0.98  
% 3.65/0.98  ------ Problem properties
% 3.65/0.98  
% 3.65/0.98  clauses:                                35
% 3.65/0.98  conjectures:                            6
% 3.65/0.98  epr:                                    9
% 3.65/0.98  horn:                                   31
% 3.65/0.98  ground:                                 7
% 3.65/0.98  unary:                                  7
% 3.65/0.98  binary:                                 16
% 3.65/0.98  lits:                                   82
% 3.65/0.98  lits_eq:                                12
% 3.65/0.98  fd_pure:                                0
% 3.65/0.98  fd_pseudo:                              0
% 3.65/0.98  fd_cond:                                2
% 3.65/0.98  fd_pseudo_cond:                         0
% 3.65/0.98  ac_symbols:                             0
% 3.65/0.98  
% 3.65/0.98  ------ Propositional Solver
% 3.65/0.98  
% 3.65/0.98  prop_solver_calls:                      29
% 3.65/0.98  prop_fast_solver_calls:                 1643
% 3.65/0.98  smt_solver_calls:                       0
% 3.65/0.98  smt_fast_solver_calls:                  0
% 3.65/0.98  prop_num_of_clauses:                    3781
% 3.65/0.98  prop_preprocess_simplified:             10442
% 3.65/0.98  prop_fo_subsumed:                       83
% 3.65/0.98  prop_solver_time:                       0.
% 3.65/0.98  smt_solver_time:                        0.
% 3.65/0.98  smt_fast_solver_time:                   0.
% 3.65/0.98  prop_fast_solver_time:                  0.
% 3.65/0.98  prop_unsat_core_time:                   0.
% 3.65/0.98  
% 3.65/0.98  ------ QBF
% 3.65/0.98  
% 3.65/0.98  qbf_q_res:                              0
% 3.65/0.98  qbf_num_tautologies:                    0
% 3.65/0.98  qbf_prep_cycles:                        0
% 3.65/0.98  
% 3.65/0.98  ------ BMC1
% 3.65/0.98  
% 3.65/0.98  bmc1_current_bound:                     -1
% 3.65/0.98  bmc1_last_solved_bound:                 -1
% 3.65/0.98  bmc1_unsat_core_size:                   -1
% 3.65/0.98  bmc1_unsat_core_parents_size:           -1
% 3.65/0.98  bmc1_merge_next_fun:                    0
% 3.65/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.65/0.98  
% 3.65/0.98  ------ Instantiation
% 3.65/0.98  
% 3.65/0.98  inst_num_of_clauses:                    1076
% 3.65/0.98  inst_num_in_passive:                    234
% 3.65/0.98  inst_num_in_active:                     524
% 3.65/0.98  inst_num_in_unprocessed:                318
% 3.65/0.98  inst_num_of_loops:                      740
% 3.65/0.98  inst_num_of_learning_restarts:          0
% 3.65/0.98  inst_num_moves_active_passive:          212
% 3.65/0.98  inst_lit_activity:                      0
% 3.65/0.98  inst_lit_activity_moves:                0
% 3.65/0.98  inst_num_tautologies:                   0
% 3.65/0.98  inst_num_prop_implied:                  0
% 3.65/0.98  inst_num_existing_simplified:           0
% 3.65/0.98  inst_num_eq_res_simplified:             0
% 3.65/0.98  inst_num_child_elim:                    0
% 3.65/0.98  inst_num_of_dismatching_blockings:      533
% 3.65/0.98  inst_num_of_non_proper_insts:           1565
% 3.65/0.98  inst_num_of_duplicates:                 0
% 3.65/0.98  inst_inst_num_from_inst_to_res:         0
% 3.65/0.98  inst_dismatching_checking_time:         0.
% 3.65/0.98  
% 3.65/0.98  ------ Resolution
% 3.65/0.98  
% 3.65/0.98  res_num_of_clauses:                     0
% 3.65/0.98  res_num_in_passive:                     0
% 3.65/0.98  res_num_in_active:                      0
% 3.65/0.98  res_num_of_loops:                       160
% 3.65/0.98  res_forward_subset_subsumed:            90
% 3.65/0.98  res_backward_subset_subsumed:           0
% 3.65/0.98  res_forward_subsumed:                   0
% 3.65/0.98  res_backward_subsumed:                  0
% 3.65/0.98  res_forward_subsumption_resolution:     3
% 3.65/0.98  res_backward_subsumption_resolution:    0
% 3.65/0.98  res_clause_to_clause_subsumption:       2109
% 3.65/0.98  res_orphan_elimination:                 0
% 3.65/0.98  res_tautology_del:                      186
% 3.65/0.98  res_num_eq_res_simplified:              0
% 3.65/0.98  res_num_sel_changes:                    0
% 3.65/0.98  res_moves_from_active_to_pass:          0
% 3.65/0.98  
% 3.65/0.98  ------ Superposition
% 3.65/0.98  
% 3.65/0.98  sup_time_total:                         0.
% 3.65/0.98  sup_time_generating:                    0.
% 3.65/0.98  sup_time_sim_full:                      0.
% 3.65/0.98  sup_time_sim_immed:                     0.
% 3.65/0.98  
% 3.65/0.98  sup_num_of_clauses:                     220
% 3.65/0.98  sup_num_in_active:                      123
% 3.65/0.98  sup_num_in_passive:                     97
% 3.65/0.98  sup_num_of_loops:                       146
% 3.65/0.98  sup_fw_superposition:                   446
% 3.65/0.98  sup_bw_superposition:                   262
% 3.65/0.98  sup_immediate_simplified:               399
% 3.65/0.98  sup_given_eliminated:                   4
% 3.65/0.98  comparisons_done:                       0
% 3.65/0.98  comparisons_avoided:                    0
% 3.65/0.98  
% 3.65/0.98  ------ Simplifications
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  sim_fw_subset_subsumed:                 39
% 3.65/0.98  sim_bw_subset_subsumed:                 8
% 3.65/0.98  sim_fw_subsumed:                        49
% 3.65/0.98  sim_bw_subsumed:                        1
% 3.65/0.98  sim_fw_subsumption_res:                 4
% 3.65/0.98  sim_bw_subsumption_res:                 2
% 3.65/0.98  sim_tautology_del:                      12
% 3.65/0.98  sim_eq_tautology_del:                   129
% 3.65/0.98  sim_eq_res_simp:                        0
% 3.65/0.98  sim_fw_demodulated:                     180
% 3.65/0.98  sim_bw_demodulated:                     24
% 3.65/0.98  sim_light_normalised:                   227
% 3.65/0.98  sim_joinable_taut:                      0
% 3.65/0.98  sim_joinable_simp:                      0
% 3.65/0.98  sim_ac_normalised:                      0
% 3.65/0.98  sim_smt_subsumption:                    0
% 3.65/0.98  
%------------------------------------------------------------------------------

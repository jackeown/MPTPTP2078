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
% DateTime   : Thu Dec  3 12:13:58 EST 2020

% Result     : Theorem 19.49s
% Output     : CNFRefutation 19.49s
% Verified   : 
% Statistics : Number of formulae       :  179 (1225 expanded)
%              Number of clauses        :  104 ( 305 expanded)
%              Number of leaves         :   19 ( 299 expanded)
%              Depth                    :   29
%              Number of atoms          :  621 (10375 expanded)
%              Number of equality atoms :  135 ( 236 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3)
        & r1_tarski(sK3,X2)
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(sK1,X3)
              | ~ r1_tarski(X3,sK2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK1,k1_tops_1(X0,sK2)) )
        & ( ? [X4] :
              ( r2_hidden(sK1,X4)
              & r1_tarski(X4,sK2)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK1,k1_tops_1(X0,sK2)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X1,k1_tops_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X2,X1] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f48,f47,f46])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1490,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1491,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_1671,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_1672,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1671])).

cnf(c_21,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_16,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_390,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_391,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_27])).

cnf(c_396,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(X0,sK2)
    | k1_tops_1(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_396])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_678,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_497])).

cnf(c_1677,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_1678,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_1734,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_31,c_32,c_1672,c_1678])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_1488,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1493,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_35,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1728,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_31,c_35,c_1672,c_1678])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1497,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1499,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2788,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_1499])).

cnf(c_7767,plain,
    ( k2_xboole_0(k1_tarski(sK1),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1728,c_2788])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1500,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7786,plain,
    ( r1_tarski(k1_tarski(sK1),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7767,c_1500])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1498,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10726,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(sK1),X1) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7786,c_1498])).

cnf(c_66389,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,X1)) = iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_10726])).

cnf(c_88367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK0,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_66389])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2037,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1494])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_520,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_521,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_466,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_467,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_581,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = X1
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_521,c_467])).

cnf(c_582,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_24,negated_conjecture,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | sK3 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_582,c_24])).

cnf(c_634,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_636,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_25])).

cnf(c_1483,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_2048,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2037])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_228,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_285,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_229])).

cnf(c_1739,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_3371,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_3397,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1483,c_26,c_636,c_1671,c_1677,c_2048,c_3371])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_1485,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_2425,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1734,c_1485])).

cnf(c_3400,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_3397,c_2425])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1501,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,k3_subset_1(X1,X0))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_229])).

cnf(c_805,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_806,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_805])).

cnf(c_852,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,k3_subset_1(X1,X0))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_286,c_806])).

cnf(c_1480,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_1944,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,k3_subset_1(X1,X0))) = iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_1480])).

cnf(c_1489,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_3711,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1489,c_1494])).

cnf(c_4904,plain,
    ( r1_tarski(X0,k3_subset_1(X1,k3_subset_1(X1,X0))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1944,c_3711])).

cnf(c_4905,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,k3_subset_1(X1,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4904])).

cnf(c_4912,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK3)) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3400,c_4905])).

cnf(c_90362,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_88367,c_2037,c_4912])).

cnf(c_90363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_90362])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1496,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_90383,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_90363,c_1496])).

cnf(c_90589,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_90383])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_90589,c_1678,c_1672,c_34,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:00:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.49/3.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.49/3.01  
% 19.49/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.49/3.01  
% 19.49/3.01  ------  iProver source info
% 19.49/3.01  
% 19.49/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.49/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.49/3.01  git: non_committed_changes: false
% 19.49/3.01  git: last_make_outside_of_git: false
% 19.49/3.01  
% 19.49/3.01  ------ 
% 19.49/3.01  
% 19.49/3.01  ------ Input Options
% 19.49/3.01  
% 19.49/3.01  --out_options                           all
% 19.49/3.01  --tptp_safe_out                         true
% 19.49/3.01  --problem_path                          ""
% 19.49/3.01  --include_path                          ""
% 19.49/3.01  --clausifier                            res/vclausify_rel
% 19.49/3.01  --clausifier_options                    --mode clausify
% 19.49/3.01  --stdin                                 false
% 19.49/3.01  --stats_out                             all
% 19.49/3.01  
% 19.49/3.01  ------ General Options
% 19.49/3.01  
% 19.49/3.01  --fof                                   false
% 19.49/3.01  --time_out_real                         305.
% 19.49/3.01  --time_out_virtual                      -1.
% 19.49/3.01  --symbol_type_check                     false
% 19.49/3.01  --clausify_out                          false
% 19.49/3.01  --sig_cnt_out                           false
% 19.49/3.01  --trig_cnt_out                          false
% 19.49/3.01  --trig_cnt_out_tolerance                1.
% 19.49/3.01  --trig_cnt_out_sk_spl                   false
% 19.49/3.01  --abstr_cl_out                          false
% 19.49/3.01  
% 19.49/3.01  ------ Global Options
% 19.49/3.01  
% 19.49/3.01  --schedule                              default
% 19.49/3.01  --add_important_lit                     false
% 19.49/3.01  --prop_solver_per_cl                    1000
% 19.49/3.01  --min_unsat_core                        false
% 19.49/3.01  --soft_assumptions                      false
% 19.49/3.01  --soft_lemma_size                       3
% 19.49/3.01  --prop_impl_unit_size                   0
% 19.49/3.01  --prop_impl_unit                        []
% 19.49/3.01  --share_sel_clauses                     true
% 19.49/3.01  --reset_solvers                         false
% 19.49/3.01  --bc_imp_inh                            [conj_cone]
% 19.49/3.01  --conj_cone_tolerance                   3.
% 19.49/3.01  --extra_neg_conj                        none
% 19.49/3.01  --large_theory_mode                     true
% 19.49/3.01  --prolific_symb_bound                   200
% 19.49/3.01  --lt_threshold                          2000
% 19.49/3.01  --clause_weak_htbl                      true
% 19.49/3.01  --gc_record_bc_elim                     false
% 19.49/3.01  
% 19.49/3.01  ------ Preprocessing Options
% 19.49/3.01  
% 19.49/3.01  --preprocessing_flag                    true
% 19.49/3.01  --time_out_prep_mult                    0.1
% 19.49/3.01  --splitting_mode                        input
% 19.49/3.01  --splitting_grd                         true
% 19.49/3.01  --splitting_cvd                         false
% 19.49/3.01  --splitting_cvd_svl                     false
% 19.49/3.01  --splitting_nvd                         32
% 19.49/3.01  --sub_typing                            true
% 19.49/3.01  --prep_gs_sim                           true
% 19.49/3.01  --prep_unflatten                        true
% 19.49/3.01  --prep_res_sim                          true
% 19.49/3.01  --prep_upred                            true
% 19.49/3.01  --prep_sem_filter                       exhaustive
% 19.49/3.01  --prep_sem_filter_out                   false
% 19.49/3.01  --pred_elim                             true
% 19.49/3.01  --res_sim_input                         true
% 19.49/3.01  --eq_ax_congr_red                       true
% 19.49/3.01  --pure_diseq_elim                       true
% 19.49/3.01  --brand_transform                       false
% 19.49/3.01  --non_eq_to_eq                          false
% 19.49/3.01  --prep_def_merge                        true
% 19.49/3.01  --prep_def_merge_prop_impl              false
% 19.49/3.01  --prep_def_merge_mbd                    true
% 19.49/3.01  --prep_def_merge_tr_red                 false
% 19.49/3.01  --prep_def_merge_tr_cl                  false
% 19.49/3.01  --smt_preprocessing                     true
% 19.49/3.01  --smt_ac_axioms                         fast
% 19.49/3.01  --preprocessed_out                      false
% 19.49/3.01  --preprocessed_stats                    false
% 19.49/3.01  
% 19.49/3.01  ------ Abstraction refinement Options
% 19.49/3.01  
% 19.49/3.01  --abstr_ref                             []
% 19.49/3.01  --abstr_ref_prep                        false
% 19.49/3.01  --abstr_ref_until_sat                   false
% 19.49/3.01  --abstr_ref_sig_restrict                funpre
% 19.49/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.49/3.01  --abstr_ref_under                       []
% 19.49/3.01  
% 19.49/3.01  ------ SAT Options
% 19.49/3.01  
% 19.49/3.01  --sat_mode                              false
% 19.49/3.01  --sat_fm_restart_options                ""
% 19.49/3.01  --sat_gr_def                            false
% 19.49/3.01  --sat_epr_types                         true
% 19.49/3.01  --sat_non_cyclic_types                  false
% 19.49/3.01  --sat_finite_models                     false
% 19.49/3.01  --sat_fm_lemmas                         false
% 19.49/3.01  --sat_fm_prep                           false
% 19.49/3.01  --sat_fm_uc_incr                        true
% 19.49/3.01  --sat_out_model                         small
% 19.49/3.01  --sat_out_clauses                       false
% 19.49/3.01  
% 19.49/3.01  ------ QBF Options
% 19.49/3.01  
% 19.49/3.01  --qbf_mode                              false
% 19.49/3.01  --qbf_elim_univ                         false
% 19.49/3.01  --qbf_dom_inst                          none
% 19.49/3.01  --qbf_dom_pre_inst                      false
% 19.49/3.01  --qbf_sk_in                             false
% 19.49/3.01  --qbf_pred_elim                         true
% 19.49/3.01  --qbf_split                             512
% 19.49/3.01  
% 19.49/3.01  ------ BMC1 Options
% 19.49/3.01  
% 19.49/3.01  --bmc1_incremental                      false
% 19.49/3.01  --bmc1_axioms                           reachable_all
% 19.49/3.01  --bmc1_min_bound                        0
% 19.49/3.01  --bmc1_max_bound                        -1
% 19.49/3.01  --bmc1_max_bound_default                -1
% 19.49/3.01  --bmc1_symbol_reachability              true
% 19.49/3.01  --bmc1_property_lemmas                  false
% 19.49/3.01  --bmc1_k_induction                      false
% 19.49/3.01  --bmc1_non_equiv_states                 false
% 19.49/3.01  --bmc1_deadlock                         false
% 19.49/3.01  --bmc1_ucm                              false
% 19.49/3.01  --bmc1_add_unsat_core                   none
% 19.49/3.01  --bmc1_unsat_core_children              false
% 19.49/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.49/3.01  --bmc1_out_stat                         full
% 19.49/3.01  --bmc1_ground_init                      false
% 19.49/3.01  --bmc1_pre_inst_next_state              false
% 19.49/3.01  --bmc1_pre_inst_state                   false
% 19.49/3.01  --bmc1_pre_inst_reach_state             false
% 19.49/3.01  --bmc1_out_unsat_core                   false
% 19.49/3.01  --bmc1_aig_witness_out                  false
% 19.49/3.01  --bmc1_verbose                          false
% 19.49/3.01  --bmc1_dump_clauses_tptp                false
% 19.49/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.49/3.01  --bmc1_dump_file                        -
% 19.49/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.49/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.49/3.01  --bmc1_ucm_extend_mode                  1
% 19.49/3.01  --bmc1_ucm_init_mode                    2
% 19.49/3.01  --bmc1_ucm_cone_mode                    none
% 19.49/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.49/3.01  --bmc1_ucm_relax_model                  4
% 19.49/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.49/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.49/3.01  --bmc1_ucm_layered_model                none
% 19.49/3.01  --bmc1_ucm_max_lemma_size               10
% 19.49/3.01  
% 19.49/3.01  ------ AIG Options
% 19.49/3.01  
% 19.49/3.01  --aig_mode                              false
% 19.49/3.01  
% 19.49/3.01  ------ Instantiation Options
% 19.49/3.01  
% 19.49/3.01  --instantiation_flag                    true
% 19.49/3.01  --inst_sos_flag                         false
% 19.49/3.01  --inst_sos_phase                        true
% 19.49/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.49/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.49/3.01  --inst_lit_sel_side                     num_symb
% 19.49/3.01  --inst_solver_per_active                1400
% 19.49/3.01  --inst_solver_calls_frac                1.
% 19.49/3.01  --inst_passive_queue_type               priority_queues
% 19.49/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.49/3.01  --inst_passive_queues_freq              [25;2]
% 19.49/3.01  --inst_dismatching                      true
% 19.49/3.01  --inst_eager_unprocessed_to_passive     true
% 19.49/3.01  --inst_prop_sim_given                   true
% 19.49/3.01  --inst_prop_sim_new                     false
% 19.49/3.01  --inst_subs_new                         false
% 19.49/3.01  --inst_eq_res_simp                      false
% 19.49/3.01  --inst_subs_given                       false
% 19.49/3.01  --inst_orphan_elimination               true
% 19.49/3.01  --inst_learning_loop_flag               true
% 19.49/3.01  --inst_learning_start                   3000
% 19.49/3.01  --inst_learning_factor                  2
% 19.49/3.01  --inst_start_prop_sim_after_learn       3
% 19.49/3.01  --inst_sel_renew                        solver
% 19.49/3.01  --inst_lit_activity_flag                true
% 19.49/3.01  --inst_restr_to_given                   false
% 19.49/3.01  --inst_activity_threshold               500
% 19.49/3.01  --inst_out_proof                        true
% 19.49/3.01  
% 19.49/3.01  ------ Resolution Options
% 19.49/3.01  
% 19.49/3.01  --resolution_flag                       true
% 19.49/3.01  --res_lit_sel                           adaptive
% 19.49/3.01  --res_lit_sel_side                      none
% 19.49/3.01  --res_ordering                          kbo
% 19.49/3.01  --res_to_prop_solver                    active
% 19.49/3.01  --res_prop_simpl_new                    false
% 19.49/3.01  --res_prop_simpl_given                  true
% 19.49/3.01  --res_passive_queue_type                priority_queues
% 19.49/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.49/3.01  --res_passive_queues_freq               [15;5]
% 19.49/3.01  --res_forward_subs                      full
% 19.49/3.01  --res_backward_subs                     full
% 19.49/3.01  --res_forward_subs_resolution           true
% 19.49/3.01  --res_backward_subs_resolution          true
% 19.49/3.01  --res_orphan_elimination                true
% 19.49/3.01  --res_time_limit                        2.
% 19.49/3.01  --res_out_proof                         true
% 19.49/3.01  
% 19.49/3.01  ------ Superposition Options
% 19.49/3.01  
% 19.49/3.01  --superposition_flag                    true
% 19.49/3.01  --sup_passive_queue_type                priority_queues
% 19.49/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.49/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.49/3.01  --demod_completeness_check              fast
% 19.49/3.01  --demod_use_ground                      true
% 19.49/3.01  --sup_to_prop_solver                    passive
% 19.49/3.01  --sup_prop_simpl_new                    true
% 19.49/3.01  --sup_prop_simpl_given                  true
% 19.49/3.01  --sup_fun_splitting                     false
% 19.49/3.01  --sup_smt_interval                      50000
% 19.49/3.01  
% 19.49/3.01  ------ Superposition Simplification Setup
% 19.49/3.01  
% 19.49/3.01  --sup_indices_passive                   []
% 19.49/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.49/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.49/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.49/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.49/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.49/3.01  --sup_full_bw                           [BwDemod]
% 19.49/3.01  --sup_immed_triv                        [TrivRules]
% 19.49/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.49/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.49/3.01  --sup_immed_bw_main                     []
% 19.49/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.49/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.49/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.49/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.49/3.01  
% 19.49/3.01  ------ Combination Options
% 19.49/3.01  
% 19.49/3.01  --comb_res_mult                         3
% 19.49/3.01  --comb_sup_mult                         2
% 19.49/3.01  --comb_inst_mult                        10
% 19.49/3.01  
% 19.49/3.01  ------ Debug Options
% 19.49/3.01  
% 19.49/3.01  --dbg_backtrace                         false
% 19.49/3.01  --dbg_dump_prop_clauses                 false
% 19.49/3.01  --dbg_dump_prop_clauses_file            -
% 19.49/3.01  --dbg_out_stat                          false
% 19.49/3.01  ------ Parsing...
% 19.49/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.49/3.01  
% 19.49/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 19.49/3.01  
% 19.49/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.49/3.01  
% 19.49/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.49/3.01  ------ Proving...
% 19.49/3.01  ------ Problem Properties 
% 19.49/3.01  
% 19.49/3.01  
% 19.49/3.01  clauses                                 23
% 19.49/3.01  conjectures                             4
% 19.49/3.01  EPR                                     3
% 19.49/3.01  Horn                                    19
% 19.49/3.01  unary                                   2
% 19.49/3.01  binary                                  13
% 19.49/3.01  lits                                    58
% 19.49/3.01  lits eq                                 6
% 19.49/3.01  fd_pure                                 0
% 19.49/3.01  fd_pseudo                               0
% 19.49/3.01  fd_cond                                 0
% 19.49/3.01  fd_pseudo_cond                          1
% 19.49/3.01  AC symbols                              0
% 19.49/3.01  
% 19.49/3.01  ------ Schedule dynamic 5 is on 
% 19.49/3.01  
% 19.49/3.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.49/3.01  
% 19.49/3.01  
% 19.49/3.01  ------ 
% 19.49/3.01  Current options:
% 19.49/3.01  ------ 
% 19.49/3.01  
% 19.49/3.01  ------ Input Options
% 19.49/3.01  
% 19.49/3.01  --out_options                           all
% 19.49/3.01  --tptp_safe_out                         true
% 19.49/3.01  --problem_path                          ""
% 19.49/3.01  --include_path                          ""
% 19.49/3.01  --clausifier                            res/vclausify_rel
% 19.49/3.01  --clausifier_options                    --mode clausify
% 19.49/3.01  --stdin                                 false
% 19.49/3.01  --stats_out                             all
% 19.49/3.01  
% 19.49/3.01  ------ General Options
% 19.49/3.01  
% 19.49/3.01  --fof                                   false
% 19.49/3.01  --time_out_real                         305.
% 19.49/3.01  --time_out_virtual                      -1.
% 19.49/3.01  --symbol_type_check                     false
% 19.49/3.01  --clausify_out                          false
% 19.49/3.01  --sig_cnt_out                           false
% 19.49/3.01  --trig_cnt_out                          false
% 19.49/3.01  --trig_cnt_out_tolerance                1.
% 19.49/3.01  --trig_cnt_out_sk_spl                   false
% 19.49/3.01  --abstr_cl_out                          false
% 19.49/3.01  
% 19.49/3.01  ------ Global Options
% 19.49/3.01  
% 19.49/3.01  --schedule                              default
% 19.49/3.01  --add_important_lit                     false
% 19.49/3.01  --prop_solver_per_cl                    1000
% 19.49/3.01  --min_unsat_core                        false
% 19.49/3.01  --soft_assumptions                      false
% 19.49/3.01  --soft_lemma_size                       3
% 19.49/3.01  --prop_impl_unit_size                   0
% 19.49/3.01  --prop_impl_unit                        []
% 19.49/3.01  --share_sel_clauses                     true
% 19.49/3.01  --reset_solvers                         false
% 19.49/3.01  --bc_imp_inh                            [conj_cone]
% 19.49/3.01  --conj_cone_tolerance                   3.
% 19.49/3.01  --extra_neg_conj                        none
% 19.49/3.01  --large_theory_mode                     true
% 19.49/3.01  --prolific_symb_bound                   200
% 19.49/3.01  --lt_threshold                          2000
% 19.49/3.01  --clause_weak_htbl                      true
% 19.49/3.01  --gc_record_bc_elim                     false
% 19.49/3.01  
% 19.49/3.01  ------ Preprocessing Options
% 19.49/3.01  
% 19.49/3.01  --preprocessing_flag                    true
% 19.49/3.01  --time_out_prep_mult                    0.1
% 19.49/3.01  --splitting_mode                        input
% 19.49/3.01  --splitting_grd                         true
% 19.49/3.01  --splitting_cvd                         false
% 19.49/3.01  --splitting_cvd_svl                     false
% 19.49/3.01  --splitting_nvd                         32
% 19.49/3.01  --sub_typing                            true
% 19.49/3.01  --prep_gs_sim                           true
% 19.49/3.01  --prep_unflatten                        true
% 19.49/3.01  --prep_res_sim                          true
% 19.49/3.01  --prep_upred                            true
% 19.49/3.01  --prep_sem_filter                       exhaustive
% 19.49/3.01  --prep_sem_filter_out                   false
% 19.49/3.01  --pred_elim                             true
% 19.49/3.01  --res_sim_input                         true
% 19.49/3.01  --eq_ax_congr_red                       true
% 19.49/3.01  --pure_diseq_elim                       true
% 19.49/3.01  --brand_transform                       false
% 19.49/3.01  --non_eq_to_eq                          false
% 19.49/3.01  --prep_def_merge                        true
% 19.49/3.01  --prep_def_merge_prop_impl              false
% 19.49/3.01  --prep_def_merge_mbd                    true
% 19.49/3.01  --prep_def_merge_tr_red                 false
% 19.49/3.01  --prep_def_merge_tr_cl                  false
% 19.49/3.01  --smt_preprocessing                     true
% 19.49/3.01  --smt_ac_axioms                         fast
% 19.49/3.01  --preprocessed_out                      false
% 19.49/3.01  --preprocessed_stats                    false
% 19.49/3.01  
% 19.49/3.01  ------ Abstraction refinement Options
% 19.49/3.01  
% 19.49/3.01  --abstr_ref                             []
% 19.49/3.01  --abstr_ref_prep                        false
% 19.49/3.01  --abstr_ref_until_sat                   false
% 19.49/3.01  --abstr_ref_sig_restrict                funpre
% 19.49/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.49/3.01  --abstr_ref_under                       []
% 19.49/3.01  
% 19.49/3.01  ------ SAT Options
% 19.49/3.01  
% 19.49/3.01  --sat_mode                              false
% 19.49/3.01  --sat_fm_restart_options                ""
% 19.49/3.01  --sat_gr_def                            false
% 19.49/3.01  --sat_epr_types                         true
% 19.49/3.01  --sat_non_cyclic_types                  false
% 19.49/3.01  --sat_finite_models                     false
% 19.49/3.01  --sat_fm_lemmas                         false
% 19.49/3.01  --sat_fm_prep                           false
% 19.49/3.01  --sat_fm_uc_incr                        true
% 19.49/3.01  --sat_out_model                         small
% 19.49/3.01  --sat_out_clauses                       false
% 19.49/3.01  
% 19.49/3.01  ------ QBF Options
% 19.49/3.01  
% 19.49/3.01  --qbf_mode                              false
% 19.49/3.01  --qbf_elim_univ                         false
% 19.49/3.01  --qbf_dom_inst                          none
% 19.49/3.01  --qbf_dom_pre_inst                      false
% 19.49/3.01  --qbf_sk_in                             false
% 19.49/3.01  --qbf_pred_elim                         true
% 19.49/3.01  --qbf_split                             512
% 19.49/3.01  
% 19.49/3.01  ------ BMC1 Options
% 19.49/3.01  
% 19.49/3.01  --bmc1_incremental                      false
% 19.49/3.01  --bmc1_axioms                           reachable_all
% 19.49/3.01  --bmc1_min_bound                        0
% 19.49/3.01  --bmc1_max_bound                        -1
% 19.49/3.01  --bmc1_max_bound_default                -1
% 19.49/3.01  --bmc1_symbol_reachability              true
% 19.49/3.01  --bmc1_property_lemmas                  false
% 19.49/3.01  --bmc1_k_induction                      false
% 19.49/3.01  --bmc1_non_equiv_states                 false
% 19.49/3.01  --bmc1_deadlock                         false
% 19.49/3.01  --bmc1_ucm                              false
% 19.49/3.01  --bmc1_add_unsat_core                   none
% 19.49/3.01  --bmc1_unsat_core_children              false
% 19.49/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.49/3.01  --bmc1_out_stat                         full
% 19.49/3.01  --bmc1_ground_init                      false
% 19.49/3.01  --bmc1_pre_inst_next_state              false
% 19.49/3.01  --bmc1_pre_inst_state                   false
% 19.49/3.01  --bmc1_pre_inst_reach_state             false
% 19.49/3.01  --bmc1_out_unsat_core                   false
% 19.49/3.01  --bmc1_aig_witness_out                  false
% 19.49/3.01  --bmc1_verbose                          false
% 19.49/3.01  --bmc1_dump_clauses_tptp                false
% 19.49/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.49/3.01  --bmc1_dump_file                        -
% 19.49/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.49/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.49/3.01  --bmc1_ucm_extend_mode                  1
% 19.49/3.01  --bmc1_ucm_init_mode                    2
% 19.49/3.01  --bmc1_ucm_cone_mode                    none
% 19.49/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.49/3.01  --bmc1_ucm_relax_model                  4
% 19.49/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.49/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.49/3.01  --bmc1_ucm_layered_model                none
% 19.49/3.01  --bmc1_ucm_max_lemma_size               10
% 19.49/3.01  
% 19.49/3.01  ------ AIG Options
% 19.49/3.01  
% 19.49/3.01  --aig_mode                              false
% 19.49/3.01  
% 19.49/3.01  ------ Instantiation Options
% 19.49/3.01  
% 19.49/3.01  --instantiation_flag                    true
% 19.49/3.01  --inst_sos_flag                         false
% 19.49/3.01  --inst_sos_phase                        true
% 19.49/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.49/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.49/3.01  --inst_lit_sel_side                     none
% 19.49/3.01  --inst_solver_per_active                1400
% 19.49/3.01  --inst_solver_calls_frac                1.
% 19.49/3.01  --inst_passive_queue_type               priority_queues
% 19.49/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.49/3.01  --inst_passive_queues_freq              [25;2]
% 19.49/3.01  --inst_dismatching                      true
% 19.49/3.01  --inst_eager_unprocessed_to_passive     true
% 19.49/3.01  --inst_prop_sim_given                   true
% 19.49/3.01  --inst_prop_sim_new                     false
% 19.49/3.01  --inst_subs_new                         false
% 19.49/3.01  --inst_eq_res_simp                      false
% 19.49/3.01  --inst_subs_given                       false
% 19.49/3.01  --inst_orphan_elimination               true
% 19.49/3.01  --inst_learning_loop_flag               true
% 19.49/3.01  --inst_learning_start                   3000
% 19.49/3.01  --inst_learning_factor                  2
% 19.49/3.01  --inst_start_prop_sim_after_learn       3
% 19.49/3.01  --inst_sel_renew                        solver
% 19.49/3.01  --inst_lit_activity_flag                true
% 19.49/3.01  --inst_restr_to_given                   false
% 19.49/3.01  --inst_activity_threshold               500
% 19.49/3.01  --inst_out_proof                        true
% 19.49/3.01  
% 19.49/3.01  ------ Resolution Options
% 19.49/3.01  
% 19.49/3.01  --resolution_flag                       false
% 19.49/3.01  --res_lit_sel                           adaptive
% 19.49/3.01  --res_lit_sel_side                      none
% 19.49/3.01  --res_ordering                          kbo
% 19.49/3.01  --res_to_prop_solver                    active
% 19.49/3.01  --res_prop_simpl_new                    false
% 19.49/3.01  --res_prop_simpl_given                  true
% 19.49/3.01  --res_passive_queue_type                priority_queues
% 19.49/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.49/3.01  --res_passive_queues_freq               [15;5]
% 19.49/3.01  --res_forward_subs                      full
% 19.49/3.01  --res_backward_subs                     full
% 19.49/3.01  --res_forward_subs_resolution           true
% 19.49/3.01  --res_backward_subs_resolution          true
% 19.49/3.01  --res_orphan_elimination                true
% 19.49/3.01  --res_time_limit                        2.
% 19.49/3.01  --res_out_proof                         true
% 19.49/3.01  
% 19.49/3.01  ------ Superposition Options
% 19.49/3.01  
% 19.49/3.01  --superposition_flag                    true
% 19.49/3.01  --sup_passive_queue_type                priority_queues
% 19.49/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.49/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.49/3.01  --demod_completeness_check              fast
% 19.49/3.01  --demod_use_ground                      true
% 19.49/3.01  --sup_to_prop_solver                    passive
% 19.49/3.01  --sup_prop_simpl_new                    true
% 19.49/3.01  --sup_prop_simpl_given                  true
% 19.49/3.01  --sup_fun_splitting                     false
% 19.49/3.01  --sup_smt_interval                      50000
% 19.49/3.01  
% 19.49/3.01  ------ Superposition Simplification Setup
% 19.49/3.01  
% 19.49/3.01  --sup_indices_passive                   []
% 19.49/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.49/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.49/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.49/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.49/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.49/3.01  --sup_full_bw                           [BwDemod]
% 19.49/3.01  --sup_immed_triv                        [TrivRules]
% 19.49/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.49/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.49/3.01  --sup_immed_bw_main                     []
% 19.49/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.49/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.49/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.49/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.49/3.01  
% 19.49/3.01  ------ Combination Options
% 19.49/3.01  
% 19.49/3.01  --comb_res_mult                         3
% 19.49/3.01  --comb_sup_mult                         2
% 19.49/3.01  --comb_inst_mult                        10
% 19.49/3.01  
% 19.49/3.01  ------ Debug Options
% 19.49/3.01  
% 19.49/3.01  --dbg_backtrace                         false
% 19.49/3.01  --dbg_dump_prop_clauses                 false
% 19.49/3.01  --dbg_dump_prop_clauses_file            -
% 19.49/3.01  --dbg_out_stat                          false
% 19.49/3.01  
% 19.49/3.01  
% 19.49/3.01  
% 19.49/3.01  
% 19.49/3.01  ------ Proving...
% 19.49/3.01  
% 19.49/3.01  
% 19.49/3.01  % SZS status Theorem for theBenchmark.p
% 19.49/3.01  
% 19.49/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.49/3.01  
% 19.49/3.01  fof(f16,conjecture,(
% 19.49/3.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f17,negated_conjecture,(
% 19.49/3.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 19.49/3.01    inference(negated_conjecture,[],[f16])).
% 19.49/3.01  
% 19.49/3.01  fof(f36,plain,(
% 19.49/3.01    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 19.49/3.01    inference(ennf_transformation,[],[f17])).
% 19.49/3.01  
% 19.49/3.01  fof(f37,plain,(
% 19.49/3.01    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.49/3.01    inference(flattening,[],[f36])).
% 19.49/3.01  
% 19.49/3.01  fof(f43,plain,(
% 19.49/3.01    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.49/3.01    inference(nnf_transformation,[],[f37])).
% 19.49/3.01  
% 19.49/3.01  fof(f44,plain,(
% 19.49/3.01    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.49/3.01    inference(flattening,[],[f43])).
% 19.49/3.01  
% 19.49/3.01  fof(f45,plain,(
% 19.49/3.01    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.49/3.01    inference(rectify,[],[f44])).
% 19.49/3.01  
% 19.49/3.01  fof(f48,plain,(
% 19.49/3.01    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.49/3.01    introduced(choice_axiom,[])).
% 19.49/3.01  
% 19.49/3.01  fof(f47,plain,(
% 19.49/3.01    ( ! [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK1,k1_tops_1(X0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK1,k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.49/3.01    introduced(choice_axiom,[])).
% 19.49/3.01  
% 19.49/3.01  fof(f46,plain,(
% 19.49/3.01    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 19.49/3.01    introduced(choice_axiom,[])).
% 19.49/3.01  
% 19.49/3.01  fof(f49,plain,(
% 19.49/3.01    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 19.49/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f48,f47,f46])).
% 19.49/3.01  
% 19.49/3.01  fof(f73,plain,(
% 19.49/3.01    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.49/3.01    inference(cnf_transformation,[],[f49])).
% 19.49/3.01  
% 19.49/3.01  fof(f74,plain,(
% 19.49/3.01    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 19.49/3.01    inference(cnf_transformation,[],[f49])).
% 19.49/3.01  
% 19.49/3.01  fof(f14,axiom,(
% 19.49/3.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f33,plain,(
% 19.49/3.01    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(ennf_transformation,[],[f14])).
% 19.49/3.01  
% 19.49/3.01  fof(f69,plain,(
% 19.49/3.01    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f33])).
% 19.49/3.01  
% 19.49/3.01  fof(f72,plain,(
% 19.49/3.01    l1_pre_topc(sK0)),
% 19.49/3.01    inference(cnf_transformation,[],[f49])).
% 19.49/3.01  
% 19.49/3.01  fof(f78,plain,(
% 19.49/3.01    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 19.49/3.01    inference(cnf_transformation,[],[f49])).
% 19.49/3.01  
% 19.49/3.01  fof(f12,axiom,(
% 19.49/3.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f30,plain,(
% 19.49/3.01    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.49/3.01    inference(ennf_transformation,[],[f12])).
% 19.49/3.01  
% 19.49/3.01  fof(f31,plain,(
% 19.49/3.01    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.49/3.01    inference(flattening,[],[f30])).
% 19.49/3.01  
% 19.49/3.01  fof(f66,plain,(
% 19.49/3.01    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f31])).
% 19.49/3.01  
% 19.49/3.01  fof(f71,plain,(
% 19.49/3.01    v2_pre_topc(sK0)),
% 19.49/3.01    inference(cnf_transformation,[],[f49])).
% 19.49/3.01  
% 19.49/3.01  fof(f11,axiom,(
% 19.49/3.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f28,plain,(
% 19.49/3.01    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.49/3.01    inference(ennf_transformation,[],[f11])).
% 19.49/3.01  
% 19.49/3.01  fof(f29,plain,(
% 19.49/3.01    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(flattening,[],[f28])).
% 19.49/3.01  
% 19.49/3.01  fof(f65,plain,(
% 19.49/3.01    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f29])).
% 19.49/3.01  
% 19.49/3.01  fof(f15,axiom,(
% 19.49/3.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f34,plain,(
% 19.49/3.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(ennf_transformation,[],[f15])).
% 19.49/3.01  
% 19.49/3.01  fof(f35,plain,(
% 19.49/3.01    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(flattening,[],[f34])).
% 19.49/3.01  
% 19.49/3.01  fof(f70,plain,(
% 19.49/3.01    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f35])).
% 19.49/3.01  
% 19.49/3.01  fof(f77,plain,(
% 19.49/3.01    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 19.49/3.01    inference(cnf_transformation,[],[f49])).
% 19.49/3.01  
% 19.49/3.01  fof(f5,axiom,(
% 19.49/3.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f40,plain,(
% 19.49/3.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 19.49/3.01    inference(nnf_transformation,[],[f5])).
% 19.49/3.01  
% 19.49/3.01  fof(f57,plain,(
% 19.49/3.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f40])).
% 19.49/3.01  
% 19.49/3.01  fof(f3,axiom,(
% 19.49/3.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f19,plain,(
% 19.49/3.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.49/3.01    inference(ennf_transformation,[],[f3])).
% 19.49/3.01  
% 19.49/3.01  fof(f54,plain,(
% 19.49/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f19])).
% 19.49/3.01  
% 19.49/3.01  fof(f2,axiom,(
% 19.49/3.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f18,plain,(
% 19.49/3.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 19.49/3.01    inference(ennf_transformation,[],[f2])).
% 19.49/3.01  
% 19.49/3.01  fof(f53,plain,(
% 19.49/3.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f18])).
% 19.49/3.01  
% 19.49/3.01  fof(f4,axiom,(
% 19.49/3.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f20,plain,(
% 19.49/3.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.49/3.01    inference(ennf_transformation,[],[f4])).
% 19.49/3.01  
% 19.49/3.01  fof(f21,plain,(
% 19.49/3.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 19.49/3.01    inference(flattening,[],[f20])).
% 19.49/3.01  
% 19.49/3.01  fof(f55,plain,(
% 19.49/3.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f21])).
% 19.49/3.01  
% 19.49/3.01  fof(f8,axiom,(
% 19.49/3.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f41,plain,(
% 19.49/3.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.49/3.01    inference(nnf_transformation,[],[f8])).
% 19.49/3.01  
% 19.49/3.01  fof(f60,plain,(
% 19.49/3.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.49/3.01    inference(cnf_transformation,[],[f41])).
% 19.49/3.01  
% 19.49/3.01  fof(f9,axiom,(
% 19.49/3.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f25,plain,(
% 19.49/3.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(ennf_transformation,[],[f9])).
% 19.49/3.01  
% 19.49/3.01  fof(f26,plain,(
% 19.49/3.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(flattening,[],[f25])).
% 19.49/3.01  
% 19.49/3.01  fof(f62,plain,(
% 19.49/3.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f26])).
% 19.49/3.01  
% 19.49/3.01  fof(f13,axiom,(
% 19.49/3.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f32,plain,(
% 19.49/3.01    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(ennf_transformation,[],[f13])).
% 19.49/3.01  
% 19.49/3.01  fof(f42,plain,(
% 19.49/3.01    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(nnf_transformation,[],[f32])).
% 19.49/3.01  
% 19.49/3.01  fof(f67,plain,(
% 19.49/3.01    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f42])).
% 19.49/3.01  
% 19.49/3.01  fof(f75,plain,(
% 19.49/3.01    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 19.49/3.01    inference(cnf_transformation,[],[f49])).
% 19.49/3.01  
% 19.49/3.01  fof(f6,axiom,(
% 19.49/3.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f22,plain,(
% 19.49/3.01    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.49/3.01    inference(ennf_transformation,[],[f6])).
% 19.49/3.01  
% 19.49/3.01  fof(f58,plain,(
% 19.49/3.01    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.49/3.01    inference(cnf_transformation,[],[f22])).
% 19.49/3.01  
% 19.49/3.01  fof(f61,plain,(
% 19.49/3.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f41])).
% 19.49/3.01  
% 19.49/3.01  fof(f10,axiom,(
% 19.49/3.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f27,plain,(
% 19.49/3.01    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.49/3.01    inference(ennf_transformation,[],[f10])).
% 19.49/3.01  
% 19.49/3.01  fof(f64,plain,(
% 19.49/3.01    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f27])).
% 19.49/3.01  
% 19.49/3.01  fof(f1,axiom,(
% 19.49/3.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f38,plain,(
% 19.49/3.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.49/3.01    inference(nnf_transformation,[],[f1])).
% 19.49/3.01  
% 19.49/3.01  fof(f39,plain,(
% 19.49/3.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.49/3.01    inference(flattening,[],[f38])).
% 19.49/3.01  
% 19.49/3.01  fof(f50,plain,(
% 19.49/3.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.49/3.01    inference(cnf_transformation,[],[f39])).
% 19.49/3.01  
% 19.49/3.01  fof(f80,plain,(
% 19.49/3.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.49/3.01    inference(equality_resolution,[],[f50])).
% 19.49/3.01  
% 19.49/3.01  fof(f7,axiom,(
% 19.49/3.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 19.49/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.49/3.01  
% 19.49/3.01  fof(f23,plain,(
% 19.49/3.01    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.49/3.01    inference(ennf_transformation,[],[f7])).
% 19.49/3.01  
% 19.49/3.01  fof(f24,plain,(
% 19.49/3.01    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.49/3.01    inference(flattening,[],[f23])).
% 19.49/3.01  
% 19.49/3.01  fof(f59,plain,(
% 19.49/3.01    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.49/3.01    inference(cnf_transformation,[],[f24])).
% 19.49/3.01  
% 19.49/3.01  fof(f56,plain,(
% 19.49/3.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 19.49/3.01    inference(cnf_transformation,[],[f40])).
% 19.49/3.01  
% 19.49/3.01  fof(f76,plain,(
% 19.49/3.01    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 19.49/3.01    inference(cnf_transformation,[],[f49])).
% 19.49/3.01  
% 19.49/3.01  cnf(c_26,negated_conjecture,
% 19.49/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.49/3.01      inference(cnf_transformation,[],[f73]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1490,plain,
% 19.49/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_25,negated_conjecture,
% 19.49/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 19.49/3.01      inference(cnf_transformation,[],[f74]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1491,plain,
% 19.49/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_31,plain,
% 19.49/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_32,plain,
% 19.49/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_19,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | r1_tarski(k1_tops_1(X1,X0),X0)
% 19.49/3.01      | ~ l1_pre_topc(X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f69]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_27,negated_conjecture,
% 19.49/3.01      ( l1_pre_topc(sK0) ),
% 19.49/3.01      inference(cnf_transformation,[],[f72]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_454,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | r1_tarski(k1_tops_1(X1,X0),X0)
% 19.49/3.01      | sK0 != X1 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_455,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_454]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1671,plain,
% 19.49/3.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 19.49/3.01      inference(instantiation,[status(thm)],[c_455]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1672,plain,
% 19.49/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_1671]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_21,negated_conjecture,
% 19.49/3.01      ( ~ v3_pre_topc(X0,sK0)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ r2_hidden(sK1,X0)
% 19.49/3.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 19.49/3.01      | ~ r1_tarski(X0,sK2) ),
% 19.49/3.01      inference(cnf_transformation,[],[f78]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_16,plain,
% 19.49/3.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 19.49/3.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.49/3.01      | ~ l1_pre_topc(X0)
% 19.49/3.01      | ~ v2_pre_topc(X0) ),
% 19.49/3.01      inference(cnf_transformation,[],[f66]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_28,negated_conjecture,
% 19.49/3.01      ( v2_pre_topc(sK0) ),
% 19.49/3.01      inference(cnf_transformation,[],[f71]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_390,plain,
% 19.49/3.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 19.49/3.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.49/3.01      | ~ l1_pre_topc(X0)
% 19.49/3.01      | sK0 != X0 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_391,plain,
% 19.49/3.01      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ l1_pre_topc(sK0) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_390]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_395,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 19.49/3.01      inference(global_propositional_subsumption,
% 19.49/3.01                [status(thm)],
% 19.49/3.01                [c_391,c_27]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_396,plain,
% 19.49/3.01      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.49/3.01      inference(renaming,[status(thm)],[c_395]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_673,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ r2_hidden(sK1,X0)
% 19.49/3.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 19.49/3.01      | ~ r1_tarski(X0,sK2)
% 19.49/3.01      | k1_tops_1(sK0,X1) != X0
% 19.49/3.01      | sK0 != sK0 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_21,c_396]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_674,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 19.49/3.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 19.49/3.01      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_673]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_15,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | ~ l1_pre_topc(X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f65]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_496,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | sK0 != X1 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_497,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_496]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_678,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
% 19.49/3.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 19.49/3.01      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 19.49/3.01      inference(global_propositional_subsumption,
% 19.49/3.01                [status(thm)],
% 19.49/3.01                [c_674,c_497]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1677,plain,
% 19.49/3.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 19.49/3.01      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 19.49/3.01      inference(instantiation,[status(thm)],[c_678]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1678,plain,
% 19.49/3.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_1677]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1734,plain,
% 19.49/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.49/3.01      inference(global_propositional_subsumption,
% 19.49/3.01                [status(thm)],
% 19.49/3.01                [c_1491,c_31,c_32,c_1672,c_1678]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_20,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | ~ r1_tarski(X0,X2)
% 19.49/3.01      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 19.49/3.01      | ~ l1_pre_topc(X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f70]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_436,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | ~ r1_tarski(X0,X2)
% 19.49/3.01      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 19.49/3.01      | sK0 != X1 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_437,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ r1_tarski(X0,X1)
% 19.49/3.01      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_436]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1488,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | r1_tarski(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_22,negated_conjecture,
% 19.49/3.01      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3) ),
% 19.49/3.01      inference(cnf_transformation,[],[f77]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1493,plain,
% 19.49/3.01      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 19.49/3.01      | r2_hidden(sK1,sK3) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_35,plain,
% 19.49/3.01      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 19.49/3.01      | r2_hidden(sK1,sK3) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1728,plain,
% 19.49/3.01      ( r2_hidden(sK1,sK3) = iProver_top ),
% 19.49/3.01      inference(global_propositional_subsumption,
% 19.49/3.01                [status(thm)],
% 19.49/3.01                [c_1493,c_31,c_35,c_1672,c_1678]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_6,plain,
% 19.49/3.01      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f57]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1497,plain,
% 19.49/3.01      ( r2_hidden(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_4,plain,
% 19.49/3.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 19.49/3.01      inference(cnf_transformation,[],[f54]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1499,plain,
% 19.49/3.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_2788,plain,
% 19.49/3.01      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 19.49/3.01      | r2_hidden(X0,X1) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1497,c_1499]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_7767,plain,
% 19.49/3.01      ( k2_xboole_0(k1_tarski(sK1),sK3) = sK3 ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1728,c_2788]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_3,plain,
% 19.49/3.01      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f53]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1500,plain,
% 19.49/3.01      ( r1_tarski(X0,X1) = iProver_top
% 19.49/3.01      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_7786,plain,
% 19.49/3.01      ( r1_tarski(k1_tarski(sK1),X0) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,X0) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_7767,c_1500]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_5,plain,
% 19.49/3.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 19.49/3.01      inference(cnf_transformation,[],[f55]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1498,plain,
% 19.49/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(X1,X2) != iProver_top
% 19.49/3.01      | r1_tarski(X0,X2) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_10726,plain,
% 19.49/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tarski(sK1),X1) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,X0) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_7786,c_1498]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_66389,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | r1_tarski(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,X1)) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,k1_tops_1(sK0,X0)) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1488,c_10726]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_88367,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,X0)) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,X0) != iProver_top
% 19.49/3.01      | r1_tarski(sK3,k1_tops_1(sK0,sK3)) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1734,c_66389]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_11,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f60]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1494,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.49/3.01      | r1_tarski(X0,X1) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_2037,plain,
% 19.49/3.01      ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1734,c_1494]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_13,plain,
% 19.49/3.01      ( ~ v4_pre_topc(X0,X1)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | ~ l1_pre_topc(X1)
% 19.49/3.01      | k2_pre_topc(X1,X0) = X0 ),
% 19.49/3.01      inference(cnf_transformation,[],[f62]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_520,plain,
% 19.49/3.01      ( ~ v4_pre_topc(X0,X1)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | k2_pre_topc(X1,X0) = X0
% 19.49/3.01      | sK0 != X1 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_521,plain,
% 19.49/3.01      ( ~ v4_pre_topc(X0,sK0)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | k2_pre_topc(sK0,X0) = X0 ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_520]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_18,plain,
% 19.49/3.01      ( ~ v3_pre_topc(X0,X1)
% 19.49/3.01      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | ~ l1_pre_topc(X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f67]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_466,plain,
% 19.49/3.01      ( ~ v3_pre_topc(X0,X1)
% 19.49/3.01      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | sK0 != X1 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_467,plain,
% 19.49/3.01      ( ~ v3_pre_topc(X0,sK0)
% 19.49/3.01      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_466]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_581,plain,
% 19.49/3.01      ( ~ v3_pre_topc(X0,sK0)
% 19.49/3.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | k2_pre_topc(sK0,X1) = X1
% 19.49/3.01      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 19.49/3.01      | sK0 != sK0 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_521,c_467]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_582,plain,
% 19.49/3.01      ( ~ v3_pre_topc(X0,sK0)
% 19.49/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_581]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_24,negated_conjecture,
% 19.49/3.01      ( v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 19.49/3.01      inference(cnf_transformation,[],[f75]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_633,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 19.49/3.01      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 19.49/3.01      | sK3 != X0
% 19.49/3.01      | sK0 != sK0 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_582,c_24]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_634,plain,
% 19.49/3.01      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 19.49/3.01      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_633]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_636,plain,
% 19.49/3.01      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 19.49/3.01      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 19.49/3.01      inference(global_propositional_subsumption,
% 19.49/3.01                [status(thm)],
% 19.49/3.01                [c_634,c_25]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1483,plain,
% 19.49/3.01      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
% 19.49/3.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_2048,plain,
% 19.49/3.01      ( r1_tarski(sK3,u1_struct_0(sK0)) ),
% 19.49/3.01      inference(predicate_to_equality_rev,[status(thm)],[c_2037]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_8,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.49/3.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 19.49/3.01      inference(cnf_transformation,[],[f58]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_10,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f61]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_228,plain,
% 19.49/3.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.49/3.01      inference(prop_impl,[status(thm)],[c_10]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_229,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.49/3.01      inference(renaming,[status(thm)],[c_228]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_285,plain,
% 19.49/3.01      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 19.49/3.01      | ~ r1_tarski(X1,X0) ),
% 19.49/3.01      inference(bin_hyper_res,[status(thm)],[c_8,c_229]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1739,plain,
% 19.49/3.01      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 19.49/3.01      inference(instantiation,[status(thm)],[c_285]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_3371,plain,
% 19.49/3.01      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | ~ r1_tarski(sK3,u1_struct_0(sK0)) ),
% 19.49/3.01      inference(instantiation,[status(thm)],[c_1739]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_3397,plain,
% 19.49/3.01      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
% 19.49/3.01      inference(global_propositional_subsumption,
% 19.49/3.01                [status(thm)],
% 19.49/3.01                [c_1483,c_26,c_636,c_1671,c_1677,c_2048,c_3371]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_14,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | ~ l1_pre_topc(X1)
% 19.49/3.01      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 19.49/3.01      inference(cnf_transformation,[],[f64]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_508,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.49/3.01      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 19.49/3.01      | sK0 != X1 ),
% 19.49/3.01      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_509,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.49/3.01      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 19.49/3.01      inference(unflattening,[status(thm)],[c_508]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1485,plain,
% 19.49/3.01      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 19.49/3.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_2425,plain,
% 19.49/3.01      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) = k1_tops_1(sK0,sK3) ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1734,c_1485]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_3400,plain,
% 19.49/3.01      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = k1_tops_1(sK0,sK3) ),
% 19.49/3.01      inference(demodulation,[status(thm)],[c_3397,c_2425]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_2,plain,
% 19.49/3.01      ( r1_tarski(X0,X0) ),
% 19.49/3.01      inference(cnf_transformation,[],[f80]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1501,plain,
% 19.49/3.01      ( r1_tarski(X0,X0) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_9,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.49/3.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.49/3.01      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 19.49/3.01      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 19.49/3.01      inference(cnf_transformation,[],[f59]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_286,plain,
% 19.49/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.49/3.01      | ~ r1_tarski(X2,X1)
% 19.49/3.01      | ~ r1_tarski(X2,k3_subset_1(X1,X0))
% 19.49/3.01      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 19.49/3.01      inference(bin_hyper_res,[status(thm)],[c_9,c_229]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_805,plain,
% 19.49/3.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.49/3.01      inference(prop_impl,[status(thm)],[c_10]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_806,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.49/3.01      inference(renaming,[status(thm)],[c_805]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_852,plain,
% 19.49/3.01      ( ~ r1_tarski(X0,X1)
% 19.49/3.01      | ~ r1_tarski(X2,X1)
% 19.49/3.01      | ~ r1_tarski(X2,k3_subset_1(X1,X0))
% 19.49/3.01      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 19.49/3.01      inference(bin_hyper_res,[status(thm)],[c_286,c_806]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1480,plain,
% 19.49/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(X2,X1) != iProver_top
% 19.49/3.01      | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top
% 19.49/3.01      | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1944,plain,
% 19.49/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(X0,k3_subset_1(X1,k3_subset_1(X1,X0))) = iProver_top
% 19.49/3.01      | r1_tarski(k3_subset_1(X1,X0),X1) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1501,c_1480]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1489,plain,
% 19.49/3.01      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 19.49/3.01      | r1_tarski(X1,X0) != iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_3711,plain,
% 19.49/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1489,c_1494]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_4904,plain,
% 19.49/3.01      ( r1_tarski(X0,k3_subset_1(X1,k3_subset_1(X1,X0))) = iProver_top
% 19.49/3.01      | r1_tarski(X0,X1) != iProver_top ),
% 19.49/3.01      inference(global_propositional_subsumption,
% 19.49/3.01                [status(thm)],
% 19.49/3.01                [c_1944,c_3711]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_4905,plain,
% 19.49/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.49/3.01      | r1_tarski(X0,k3_subset_1(X1,k3_subset_1(X1,X0))) = iProver_top ),
% 19.49/3.01      inference(renaming,[status(thm)],[c_4904]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_4912,plain,
% 19.49/3.01      ( r1_tarski(sK3,k1_tops_1(sK0,sK3)) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_3400,c_4905]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_90362,plain,
% 19.49/3.01      ( r1_tarski(sK3,X0) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,X0)) = iProver_top
% 19.49/3.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.49/3.01      inference(global_propositional_subsumption,
% 19.49/3.01                [status(thm)],
% 19.49/3.01                [c_88367,c_2037,c_4912]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_90363,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,X0)) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,X0) != iProver_top ),
% 19.49/3.01      inference(renaming,[status(thm)],[c_90362]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_7,plain,
% 19.49/3.01      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 19.49/3.01      inference(cnf_transformation,[],[f56]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_1496,plain,
% 19.49/3.01      ( r2_hidden(X0,X1) = iProver_top
% 19.49/3.01      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_90383,plain,
% 19.49/3.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.49/3.01      | r2_hidden(sK1,k1_tops_1(sK0,X0)) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,X0) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_90363,c_1496]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_90589,plain,
% 19.49/3.01      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,sK2) != iProver_top ),
% 19.49/3.01      inference(superposition,[status(thm)],[c_1490,c_90383]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_23,negated_conjecture,
% 19.49/3.01      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(sK3,sK2) ),
% 19.49/3.01      inference(cnf_transformation,[],[f76]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(c_34,plain,
% 19.49/3.01      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 19.49/3.01      | r1_tarski(sK3,sK2) = iProver_top ),
% 19.49/3.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.49/3.01  
% 19.49/3.01  cnf(contradiction,plain,
% 19.49/3.01      ( $false ),
% 19.49/3.01      inference(minisat,[status(thm)],[c_90589,c_1678,c_1672,c_34,c_31]) ).
% 19.49/3.01  
% 19.49/3.01  
% 19.49/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.49/3.01  
% 19.49/3.01  ------                               Statistics
% 19.49/3.01  
% 19.49/3.01  ------ General
% 19.49/3.01  
% 19.49/3.01  abstr_ref_over_cycles:                  0
% 19.49/3.01  abstr_ref_under_cycles:                 0
% 19.49/3.01  gc_basic_clause_elim:                   0
% 19.49/3.01  forced_gc_time:                         0
% 19.49/3.01  parsing_time:                           0.008
% 19.49/3.01  unif_index_cands_time:                  0.
% 19.49/3.01  unif_index_add_time:                    0.
% 19.49/3.01  orderings_time:                         0.
% 19.49/3.01  out_proof_time:                         0.022
% 19.49/3.01  total_time:                             2.308
% 19.49/3.01  num_of_symbols:                         49
% 19.49/3.01  num_of_terms:                           70800
% 19.49/3.01  
% 19.49/3.01  ------ Preprocessing
% 19.49/3.01  
% 19.49/3.01  num_of_splits:                          0
% 19.49/3.01  num_of_split_atoms:                     0
% 19.49/3.01  num_of_reused_defs:                     0
% 19.49/3.01  num_eq_ax_congr_red:                    11
% 19.49/3.01  num_of_sem_filtered_clauses:            1
% 19.49/3.01  num_of_subtypes:                        0
% 19.49/3.01  monotx_restored_types:                  0
% 19.49/3.01  sat_num_of_epr_types:                   0
% 19.49/3.01  sat_num_of_non_cyclic_types:            0
% 19.49/3.01  sat_guarded_non_collapsed_types:        0
% 19.49/3.01  num_pure_diseq_elim:                    0
% 19.49/3.01  simp_replaced_by:                       0
% 19.49/3.01  res_preprocessed:                       118
% 19.49/3.01  prep_upred:                             0
% 19.49/3.01  prep_unflattend:                        15
% 19.49/3.01  smt_new_axioms:                         0
% 19.49/3.01  pred_elim_cands:                        3
% 19.49/3.01  pred_elim:                              4
% 19.49/3.01  pred_elim_cl:                           5
% 19.49/3.01  pred_elim_cycles:                       6
% 19.49/3.01  merged_defs:                            16
% 19.49/3.01  merged_defs_ncl:                        0
% 19.49/3.01  bin_hyper_res:                          19
% 19.49/3.01  prep_cycles:                            4
% 19.49/3.01  pred_elim_time:                         0.004
% 19.49/3.01  splitting_time:                         0.
% 19.49/3.01  sem_filter_time:                        0.
% 19.49/3.01  monotx_time:                            0.
% 19.49/3.01  subtype_inf_time:                       0.
% 19.49/3.01  
% 19.49/3.01  ------ Problem properties
% 19.49/3.01  
% 19.49/3.01  clauses:                                23
% 19.49/3.01  conjectures:                            4
% 19.49/3.01  epr:                                    3
% 19.49/3.01  horn:                                   19
% 19.49/3.01  ground:                                 5
% 19.49/3.01  unary:                                  2
% 19.49/3.01  binary:                                 13
% 19.49/3.01  lits:                                   58
% 19.49/3.01  lits_eq:                                6
% 19.49/3.01  fd_pure:                                0
% 19.49/3.01  fd_pseudo:                              0
% 19.49/3.01  fd_cond:                                0
% 19.49/3.01  fd_pseudo_cond:                         1
% 19.49/3.01  ac_symbols:                             0
% 19.49/3.01  
% 19.49/3.01  ------ Propositional Solver
% 19.49/3.01  
% 19.49/3.01  prop_solver_calls:                      37
% 19.49/3.01  prop_fast_solver_calls:                 1858
% 19.49/3.01  smt_solver_calls:                       0
% 19.49/3.01  smt_fast_solver_calls:                  0
% 19.49/3.01  prop_num_of_clauses:                    35590
% 19.49/3.01  prop_preprocess_simplified:             44113
% 19.49/3.01  prop_fo_subsumed:                       69
% 19.49/3.01  prop_solver_time:                       0.
% 19.49/3.01  smt_solver_time:                        0.
% 19.49/3.01  smt_fast_solver_time:                   0.
% 19.49/3.01  prop_fast_solver_time:                  0.
% 19.49/3.01  prop_unsat_core_time:                   0.005
% 19.49/3.01  
% 19.49/3.01  ------ QBF
% 19.49/3.01  
% 19.49/3.01  qbf_q_res:                              0
% 19.49/3.01  qbf_num_tautologies:                    0
% 19.49/3.01  qbf_prep_cycles:                        0
% 19.49/3.01  
% 19.49/3.01  ------ BMC1
% 19.49/3.01  
% 19.49/3.01  bmc1_current_bound:                     -1
% 19.49/3.01  bmc1_last_solved_bound:                 -1
% 19.49/3.01  bmc1_unsat_core_size:                   -1
% 19.49/3.01  bmc1_unsat_core_parents_size:           -1
% 19.49/3.01  bmc1_merge_next_fun:                    0
% 19.49/3.01  bmc1_unsat_core_clauses_time:           0.
% 19.49/3.01  
% 19.49/3.01  ------ Instantiation
% 19.49/3.01  
% 19.49/3.01  inst_num_of_clauses:                    8160
% 19.49/3.01  inst_num_in_passive:                    2395
% 19.49/3.01  inst_num_in_active:                     2373
% 19.49/3.01  inst_num_in_unprocessed:                3396
% 19.49/3.01  inst_num_of_loops:                      2530
% 19.49/3.01  inst_num_of_learning_restarts:          0
% 19.49/3.01  inst_num_moves_active_passive:          155
% 19.49/3.01  inst_lit_activity:                      0
% 19.49/3.01  inst_lit_activity_moves:                3
% 19.49/3.01  inst_num_tautologies:                   0
% 19.49/3.01  inst_num_prop_implied:                  0
% 19.49/3.01  inst_num_existing_simplified:           0
% 19.49/3.01  inst_num_eq_res_simplified:             0
% 19.49/3.01  inst_num_child_elim:                    0
% 19.49/3.01  inst_num_of_dismatching_blockings:      7486
% 19.49/3.01  inst_num_of_non_proper_insts:           11032
% 19.49/3.01  inst_num_of_duplicates:                 0
% 19.49/3.01  inst_inst_num_from_inst_to_res:         0
% 19.49/3.01  inst_dismatching_checking_time:         0.
% 19.49/3.01  
% 19.49/3.01  ------ Resolution
% 19.49/3.01  
% 19.49/3.01  res_num_of_clauses:                     0
% 19.49/3.01  res_num_in_passive:                     0
% 19.49/3.01  res_num_in_active:                      0
% 19.49/3.01  res_num_of_loops:                       122
% 19.49/3.01  res_forward_subset_subsumed:            197
% 19.49/3.01  res_backward_subset_subsumed:           12
% 19.49/3.01  res_forward_subsumed:                   0
% 19.49/3.01  res_backward_subsumed:                  0
% 19.49/3.01  res_forward_subsumption_resolution:     0
% 19.49/3.01  res_backward_subsumption_resolution:    0
% 19.49/3.02  res_clause_to_clause_subsumption:       29124
% 19.49/3.02  res_orphan_elimination:                 0
% 19.49/3.02  res_tautology_del:                      457
% 19.49/3.02  res_num_eq_res_simplified:              0
% 19.49/3.02  res_num_sel_changes:                    0
% 19.49/3.02  res_moves_from_active_to_pass:          0
% 19.49/3.02  
% 19.49/3.02  ------ Superposition
% 19.49/3.02  
% 19.49/3.02  sup_time_total:                         0.
% 19.49/3.02  sup_time_generating:                    0.
% 19.49/3.02  sup_time_sim_full:                      0.
% 19.49/3.02  sup_time_sim_immed:                     0.
% 19.49/3.02  
% 19.49/3.02  sup_num_of_clauses:                     3678
% 19.49/3.02  sup_num_in_active:                      473
% 19.49/3.02  sup_num_in_passive:                     3205
% 19.49/3.02  sup_num_of_loops:                       504
% 19.49/3.02  sup_fw_superposition:                   4184
% 19.49/3.02  sup_bw_superposition:                   2641
% 19.49/3.02  sup_immediate_simplified:               1897
% 19.49/3.02  sup_given_eliminated:                   1
% 19.49/3.02  comparisons_done:                       0
% 19.49/3.02  comparisons_avoided:                    0
% 19.49/3.02  
% 19.49/3.02  ------ Simplifications
% 19.49/3.02  
% 19.49/3.02  
% 19.49/3.02  sim_fw_subset_subsumed:                 455
% 19.49/3.02  sim_bw_subset_subsumed:                 87
% 19.49/3.02  sim_fw_subsumed:                        277
% 19.49/3.02  sim_bw_subsumed:                        16
% 19.49/3.02  sim_fw_subsumption_res:                 0
% 19.49/3.02  sim_bw_subsumption_res:                 0
% 19.49/3.02  sim_tautology_del:                      50
% 19.49/3.02  sim_eq_tautology_del:                   152
% 19.49/3.02  sim_eq_res_simp:                        0
% 19.49/3.02  sim_fw_demodulated:                     489
% 19.49/3.02  sim_bw_demodulated:                     30
% 19.49/3.02  sim_light_normalised:                   725
% 19.49/3.02  sim_joinable_taut:                      0
% 19.49/3.02  sim_joinable_simp:                      0
% 19.49/3.02  sim_ac_normalised:                      0
% 19.49/3.02  sim_smt_subsumption:                    0
% 19.49/3.02  
%------------------------------------------------------------------------------

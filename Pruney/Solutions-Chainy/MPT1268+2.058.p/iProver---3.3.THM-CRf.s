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
% DateTime   : Thu Dec  3 12:15:13 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  165 (1495 expanded)
%              Number of clauses        :  107 ( 368 expanded)
%              Number of leaves         :   17 ( 376 expanded)
%              Depth                    :   30
%              Number of atoms          :  642 (12978 expanded)
%              Number of equality atoms :  185 (2195 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK3
        & v3_pre_topc(sK3,X0)
        & r1_tarski(sK3,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
              & r1_tarski(X2,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tops_1(sK2,X0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,X0)
              | ~ r1_tarski(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tops_1(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
                & v3_pre_topc(X2,sK1)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
            | ~ v2_tops_1(X1,sK1) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK1)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            | v2_tops_1(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ( k1_xboole_0 != sK3
        & v3_pre_topc(sK3,sK1)
        & r1_tarski(sK3,sK2)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ v2_tops_1(sK2,sK1) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK1)
          | ~ r1_tarski(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | v2_tops_1(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tops_1(sK2,sK1) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK1)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_tops_1(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,
    ( r1_tarski(sK3,sK2)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,
    ( k1_xboole_0 != sK3
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1805,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1807,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_389,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_390,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_394,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_21])).

cnf(c_395,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_429,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_395,c_21])).

cnf(c_430,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1295,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_430])).

cnf(c_1801,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_1296,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_430])).

cnf(c_1327,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_1328,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_364,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_365,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_21])).

cnf(c_370,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_507,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_370,c_21])).

cnf(c_508,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_508])).

cnf(c_1795,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_2173,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1795])).

cnf(c_3088,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | k1_tops_1(sK1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1801,c_1327,c_1328,c_2173])).

cnf(c_3089,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3088])).

cnf(c_3096,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v2_tops_1(sK2,sK1) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_3089])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_462,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_463,plain,
    ( v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_763,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_463])).

cnf(c_764,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_766,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_20])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_791,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_463])).

cnf(c_792,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_794,plain,
    ( v3_pre_topc(sK3,sK1)
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_792,c_20])).

cnf(c_1385,plain,
    ( k1_tops_1(sK1,X0) = X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1295,c_1292,c_1296])).

cnf(c_1386,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_1385])).

cnf(c_2665,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_447,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_448,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_1799,plain,
    ( k1_tops_1(sK1,X0) = k1_xboole_0
    | v2_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_2937,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1799])).

cnf(c_8,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_346,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_347,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_21])).

cnf(c_352,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_1970,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_1976,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1997,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1299,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2049,plain,
    ( k1_tops_1(sK1,sK2) != X0
    | k1_tops_1(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_2208,plain,
    ( k1_tops_1(sK1,sK2) != k1_tops_1(sK1,sK2)
    | k1_tops_1(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2049])).

cnf(c_1298,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2209,plain,
    ( k1_tops_1(sK1,sK2) = k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2073,plain,
    ( r1_tarski(X0,u1_struct_0(sK1))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2239,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1))
    | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_19,negated_conjecture,
    ( v2_tops_1(sK2,sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2301,plain,
    ( v2_tops_1(sK2,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | k1_xboole_0 = k1_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2482,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2958,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2937])).

cnf(c_2992,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2937,c_20,c_1970,c_1976,c_1997,c_2208,c_2209,c_2239,c_2301,c_2482,c_2958])).

cnf(c_3159,plain,
    ( k1_tops_1(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3096,c_20,c_766,c_794,c_1970,c_1976,c_1997,c_2208,c_2209,c_2239,c_2301,c_2482,c_2665,c_2958])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_1797,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_3191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3159,c_1797])).

cnf(c_768,plain,
    ( k1_tops_1(sK1,sK2) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_4379,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3191,c_20,c_768,c_1970,c_1976,c_1997,c_2208,c_2209,c_2239,c_2301,c_2482,c_2958])).

cnf(c_4390,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_4379])).

cnf(c_4393,plain,
    ( r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4390,c_2992])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK2)
    | k1_tops_1(sK1,X0) != k1_xboole_0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_463])).

cnf(c_778,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK2)
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_780,plain,
    ( r1_tarski(sK3,sK2)
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_778,c_20])).

cnf(c_782,plain,
    ( k1_tops_1(sK1,sK2) != k1_xboole_0
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_4822,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4393,c_20,c_782,c_1970,c_1976,c_1997,c_2208,c_2209,c_2239,c_2301,c_2482,c_2958])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1813,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1814,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2380,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1814])).

cnf(c_4830,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4822,c_2380])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_327,plain,
    ( ~ r1_tarski(X0,X1)
    | X2 != X0
    | sK0(X2) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,sK0(X0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_1804,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,sK0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_6093,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4830,c_1804])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0
    | sK1 != sK1
    | sK2 != X0
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_463])).

cnf(c_806,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_808,plain,
    ( k1_tops_1(sK1,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_806,c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6093,c_2992,c_808])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:02:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.84/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.00  
% 2.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/1.00  
% 2.84/1.00  ------  iProver source info
% 2.84/1.00  
% 2.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/1.00  git: non_committed_changes: false
% 2.84/1.00  git: last_make_outside_of_git: false
% 2.84/1.00  
% 2.84/1.00  ------ 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options
% 2.84/1.00  
% 2.84/1.00  --out_options                           all
% 2.84/1.00  --tptp_safe_out                         true
% 2.84/1.00  --problem_path                          ""
% 2.84/1.00  --include_path                          ""
% 2.84/1.00  --clausifier                            res/vclausify_rel
% 2.84/1.00  --clausifier_options                    --mode clausify
% 2.84/1.00  --stdin                                 false
% 2.84/1.00  --stats_out                             all
% 2.84/1.00  
% 2.84/1.00  ------ General Options
% 2.84/1.00  
% 2.84/1.00  --fof                                   false
% 2.84/1.00  --time_out_real                         305.
% 2.84/1.00  --time_out_virtual                      -1.
% 2.84/1.00  --symbol_type_check                     false
% 2.84/1.00  --clausify_out                          false
% 2.84/1.00  --sig_cnt_out                           false
% 2.84/1.00  --trig_cnt_out                          false
% 2.84/1.00  --trig_cnt_out_tolerance                1.
% 2.84/1.00  --trig_cnt_out_sk_spl                   false
% 2.84/1.00  --abstr_cl_out                          false
% 2.84/1.00  
% 2.84/1.00  ------ Global Options
% 2.84/1.00  
% 2.84/1.00  --schedule                              default
% 2.84/1.00  --add_important_lit                     false
% 2.84/1.00  --prop_solver_per_cl                    1000
% 2.84/1.00  --min_unsat_core                        false
% 2.84/1.00  --soft_assumptions                      false
% 2.84/1.00  --soft_lemma_size                       3
% 2.84/1.00  --prop_impl_unit_size                   0
% 2.84/1.00  --prop_impl_unit                        []
% 2.84/1.00  --share_sel_clauses                     true
% 2.84/1.00  --reset_solvers                         false
% 2.84/1.00  --bc_imp_inh                            [conj_cone]
% 2.84/1.00  --conj_cone_tolerance                   3.
% 2.84/1.00  --extra_neg_conj                        none
% 2.84/1.00  --large_theory_mode                     true
% 2.84/1.00  --prolific_symb_bound                   200
% 2.84/1.00  --lt_threshold                          2000
% 2.84/1.00  --clause_weak_htbl                      true
% 2.84/1.00  --gc_record_bc_elim                     false
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing Options
% 2.84/1.00  
% 2.84/1.00  --preprocessing_flag                    true
% 2.84/1.00  --time_out_prep_mult                    0.1
% 2.84/1.00  --splitting_mode                        input
% 2.84/1.00  --splitting_grd                         true
% 2.84/1.00  --splitting_cvd                         false
% 2.84/1.00  --splitting_cvd_svl                     false
% 2.84/1.00  --splitting_nvd                         32
% 2.84/1.00  --sub_typing                            true
% 2.84/1.00  --prep_gs_sim                           true
% 2.84/1.00  --prep_unflatten                        true
% 2.84/1.00  --prep_res_sim                          true
% 2.84/1.00  --prep_upred                            true
% 2.84/1.00  --prep_sem_filter                       exhaustive
% 2.84/1.00  --prep_sem_filter_out                   false
% 2.84/1.00  --pred_elim                             true
% 2.84/1.00  --res_sim_input                         true
% 2.84/1.00  --eq_ax_congr_red                       true
% 2.84/1.00  --pure_diseq_elim                       true
% 2.84/1.00  --brand_transform                       false
% 2.84/1.00  --non_eq_to_eq                          false
% 2.84/1.00  --prep_def_merge                        true
% 2.84/1.00  --prep_def_merge_prop_impl              false
% 2.84/1.00  --prep_def_merge_mbd                    true
% 2.84/1.00  --prep_def_merge_tr_red                 false
% 2.84/1.00  --prep_def_merge_tr_cl                  false
% 2.84/1.00  --smt_preprocessing                     true
% 2.84/1.00  --smt_ac_axioms                         fast
% 2.84/1.00  --preprocessed_out                      false
% 2.84/1.00  --preprocessed_stats                    false
% 2.84/1.00  
% 2.84/1.00  ------ Abstraction refinement Options
% 2.84/1.00  
% 2.84/1.00  --abstr_ref                             []
% 2.84/1.00  --abstr_ref_prep                        false
% 2.84/1.00  --abstr_ref_until_sat                   false
% 2.84/1.00  --abstr_ref_sig_restrict                funpre
% 2.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.00  --abstr_ref_under                       []
% 2.84/1.00  
% 2.84/1.00  ------ SAT Options
% 2.84/1.00  
% 2.84/1.00  --sat_mode                              false
% 2.84/1.00  --sat_fm_restart_options                ""
% 2.84/1.00  --sat_gr_def                            false
% 2.84/1.00  --sat_epr_types                         true
% 2.84/1.00  --sat_non_cyclic_types                  false
% 2.84/1.00  --sat_finite_models                     false
% 2.84/1.00  --sat_fm_lemmas                         false
% 2.84/1.00  --sat_fm_prep                           false
% 2.84/1.00  --sat_fm_uc_incr                        true
% 2.84/1.00  --sat_out_model                         small
% 2.84/1.00  --sat_out_clauses                       false
% 2.84/1.00  
% 2.84/1.00  ------ QBF Options
% 2.84/1.00  
% 2.84/1.00  --qbf_mode                              false
% 2.84/1.00  --qbf_elim_univ                         false
% 2.84/1.00  --qbf_dom_inst                          none
% 2.84/1.00  --qbf_dom_pre_inst                      false
% 2.84/1.00  --qbf_sk_in                             false
% 2.84/1.00  --qbf_pred_elim                         true
% 2.84/1.00  --qbf_split                             512
% 2.84/1.00  
% 2.84/1.00  ------ BMC1 Options
% 2.84/1.00  
% 2.84/1.00  --bmc1_incremental                      false
% 2.84/1.00  --bmc1_axioms                           reachable_all
% 2.84/1.00  --bmc1_min_bound                        0
% 2.84/1.00  --bmc1_max_bound                        -1
% 2.84/1.00  --bmc1_max_bound_default                -1
% 2.84/1.00  --bmc1_symbol_reachability              true
% 2.84/1.00  --bmc1_property_lemmas                  false
% 2.84/1.00  --bmc1_k_induction                      false
% 2.84/1.00  --bmc1_non_equiv_states                 false
% 2.84/1.00  --bmc1_deadlock                         false
% 2.84/1.00  --bmc1_ucm                              false
% 2.84/1.00  --bmc1_add_unsat_core                   none
% 2.84/1.00  --bmc1_unsat_core_children              false
% 2.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.00  --bmc1_out_stat                         full
% 2.84/1.00  --bmc1_ground_init                      false
% 2.84/1.00  --bmc1_pre_inst_next_state              false
% 2.84/1.00  --bmc1_pre_inst_state                   false
% 2.84/1.00  --bmc1_pre_inst_reach_state             false
% 2.84/1.00  --bmc1_out_unsat_core                   false
% 2.84/1.00  --bmc1_aig_witness_out                  false
% 2.84/1.00  --bmc1_verbose                          false
% 2.84/1.00  --bmc1_dump_clauses_tptp                false
% 2.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.00  --bmc1_dump_file                        -
% 2.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.00  --bmc1_ucm_extend_mode                  1
% 2.84/1.00  --bmc1_ucm_init_mode                    2
% 2.84/1.00  --bmc1_ucm_cone_mode                    none
% 2.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.00  --bmc1_ucm_relax_model                  4
% 2.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.00  --bmc1_ucm_layered_model                none
% 2.84/1.00  --bmc1_ucm_max_lemma_size               10
% 2.84/1.00  
% 2.84/1.00  ------ AIG Options
% 2.84/1.00  
% 2.84/1.00  --aig_mode                              false
% 2.84/1.00  
% 2.84/1.00  ------ Instantiation Options
% 2.84/1.00  
% 2.84/1.00  --instantiation_flag                    true
% 2.84/1.00  --inst_sos_flag                         false
% 2.84/1.00  --inst_sos_phase                        true
% 2.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel_side                     num_symb
% 2.84/1.00  --inst_solver_per_active                1400
% 2.84/1.00  --inst_solver_calls_frac                1.
% 2.84/1.00  --inst_passive_queue_type               priority_queues
% 2.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.00  --inst_passive_queues_freq              [25;2]
% 2.84/1.00  --inst_dismatching                      true
% 2.84/1.00  --inst_eager_unprocessed_to_passive     true
% 2.84/1.00  --inst_prop_sim_given                   true
% 2.84/1.00  --inst_prop_sim_new                     false
% 2.84/1.00  --inst_subs_new                         false
% 2.84/1.00  --inst_eq_res_simp                      false
% 2.84/1.00  --inst_subs_given                       false
% 2.84/1.00  --inst_orphan_elimination               true
% 2.84/1.00  --inst_learning_loop_flag               true
% 2.84/1.00  --inst_learning_start                   3000
% 2.84/1.00  --inst_learning_factor                  2
% 2.84/1.00  --inst_start_prop_sim_after_learn       3
% 2.84/1.00  --inst_sel_renew                        solver
% 2.84/1.00  --inst_lit_activity_flag                true
% 2.84/1.00  --inst_restr_to_given                   false
% 2.84/1.00  --inst_activity_threshold               500
% 2.84/1.00  --inst_out_proof                        true
% 2.84/1.00  
% 2.84/1.00  ------ Resolution Options
% 2.84/1.00  
% 2.84/1.00  --resolution_flag                       true
% 2.84/1.00  --res_lit_sel                           adaptive
% 2.84/1.00  --res_lit_sel_side                      none
% 2.84/1.00  --res_ordering                          kbo
% 2.84/1.00  --res_to_prop_solver                    active
% 2.84/1.00  --res_prop_simpl_new                    false
% 2.84/1.00  --res_prop_simpl_given                  true
% 2.84/1.00  --res_passive_queue_type                priority_queues
% 2.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.00  --res_passive_queues_freq               [15;5]
% 2.84/1.00  --res_forward_subs                      full
% 2.84/1.00  --res_backward_subs                     full
% 2.84/1.00  --res_forward_subs_resolution           true
% 2.84/1.00  --res_backward_subs_resolution          true
% 2.84/1.00  --res_orphan_elimination                true
% 2.84/1.00  --res_time_limit                        2.
% 2.84/1.00  --res_out_proof                         true
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Options
% 2.84/1.00  
% 2.84/1.00  --superposition_flag                    true
% 2.84/1.00  --sup_passive_queue_type                priority_queues
% 2.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.00  --demod_completeness_check              fast
% 2.84/1.00  --demod_use_ground                      true
% 2.84/1.00  --sup_to_prop_solver                    passive
% 2.84/1.00  --sup_prop_simpl_new                    true
% 2.84/1.00  --sup_prop_simpl_given                  true
% 2.84/1.00  --sup_fun_splitting                     false
% 2.84/1.00  --sup_smt_interval                      50000
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Simplification Setup
% 2.84/1.00  
% 2.84/1.00  --sup_indices_passive                   []
% 2.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_full_bw                           [BwDemod]
% 2.84/1.00  --sup_immed_triv                        [TrivRules]
% 2.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_immed_bw_main                     []
% 2.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  
% 2.84/1.00  ------ Combination Options
% 2.84/1.00  
% 2.84/1.00  --comb_res_mult                         3
% 2.84/1.00  --comb_sup_mult                         2
% 2.84/1.00  --comb_inst_mult                        10
% 2.84/1.00  
% 2.84/1.00  ------ Debug Options
% 2.84/1.00  
% 2.84/1.00  --dbg_backtrace                         false
% 2.84/1.00  --dbg_dump_prop_clauses                 false
% 2.84/1.00  --dbg_dump_prop_clauses_file            -
% 2.84/1.00  --dbg_out_stat                          false
% 2.84/1.00  ------ Parsing...
% 2.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.84/1.00  ------ Proving...
% 2.84/1.00  ------ Problem Properties 
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  clauses                                 24
% 2.84/1.00  conjectures                             6
% 2.84/1.00  EPR                                     7
% 2.84/1.00  Horn                                    21
% 2.84/1.00  unary                                   2
% 2.84/1.00  binary                                  15
% 2.84/1.00  lits                                    58
% 2.84/1.00  lits eq                                 11
% 2.84/1.00  fd_pure                                 0
% 2.84/1.00  fd_pseudo                               0
% 2.84/1.00  fd_cond                                 4
% 2.84/1.00  fd_pseudo_cond                          0
% 2.84/1.00  AC symbols                              0
% 2.84/1.00  
% 2.84/1.00  ------ Schedule dynamic 5 is on 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  ------ 
% 2.84/1.00  Current options:
% 2.84/1.00  ------ 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options
% 2.84/1.00  
% 2.84/1.00  --out_options                           all
% 2.84/1.00  --tptp_safe_out                         true
% 2.84/1.00  --problem_path                          ""
% 2.84/1.00  --include_path                          ""
% 2.84/1.00  --clausifier                            res/vclausify_rel
% 2.84/1.00  --clausifier_options                    --mode clausify
% 2.84/1.00  --stdin                                 false
% 2.84/1.00  --stats_out                             all
% 2.84/1.00  
% 2.84/1.00  ------ General Options
% 2.84/1.00  
% 2.84/1.00  --fof                                   false
% 2.84/1.00  --time_out_real                         305.
% 2.84/1.00  --time_out_virtual                      -1.
% 2.84/1.00  --symbol_type_check                     false
% 2.84/1.00  --clausify_out                          false
% 2.84/1.00  --sig_cnt_out                           false
% 2.84/1.00  --trig_cnt_out                          false
% 2.84/1.00  --trig_cnt_out_tolerance                1.
% 2.84/1.00  --trig_cnt_out_sk_spl                   false
% 2.84/1.00  --abstr_cl_out                          false
% 2.84/1.00  
% 2.84/1.00  ------ Global Options
% 2.84/1.00  
% 2.84/1.00  --schedule                              default
% 2.84/1.00  --add_important_lit                     false
% 2.84/1.00  --prop_solver_per_cl                    1000
% 2.84/1.00  --min_unsat_core                        false
% 2.84/1.00  --soft_assumptions                      false
% 2.84/1.00  --soft_lemma_size                       3
% 2.84/1.00  --prop_impl_unit_size                   0
% 2.84/1.00  --prop_impl_unit                        []
% 2.84/1.00  --share_sel_clauses                     true
% 2.84/1.00  --reset_solvers                         false
% 2.84/1.00  --bc_imp_inh                            [conj_cone]
% 2.84/1.00  --conj_cone_tolerance                   3.
% 2.84/1.00  --extra_neg_conj                        none
% 2.84/1.00  --large_theory_mode                     true
% 2.84/1.00  --prolific_symb_bound                   200
% 2.84/1.00  --lt_threshold                          2000
% 2.84/1.00  --clause_weak_htbl                      true
% 2.84/1.00  --gc_record_bc_elim                     false
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing Options
% 2.84/1.00  
% 2.84/1.00  --preprocessing_flag                    true
% 2.84/1.00  --time_out_prep_mult                    0.1
% 2.84/1.00  --splitting_mode                        input
% 2.84/1.00  --splitting_grd                         true
% 2.84/1.00  --splitting_cvd                         false
% 2.84/1.00  --splitting_cvd_svl                     false
% 2.84/1.00  --splitting_nvd                         32
% 2.84/1.00  --sub_typing                            true
% 2.84/1.00  --prep_gs_sim                           true
% 2.84/1.00  --prep_unflatten                        true
% 2.84/1.00  --prep_res_sim                          true
% 2.84/1.00  --prep_upred                            true
% 2.84/1.00  --prep_sem_filter                       exhaustive
% 2.84/1.00  --prep_sem_filter_out                   false
% 2.84/1.00  --pred_elim                             true
% 2.84/1.00  --res_sim_input                         true
% 2.84/1.00  --eq_ax_congr_red                       true
% 2.84/1.00  --pure_diseq_elim                       true
% 2.84/1.00  --brand_transform                       false
% 2.84/1.00  --non_eq_to_eq                          false
% 2.84/1.00  --prep_def_merge                        true
% 2.84/1.00  --prep_def_merge_prop_impl              false
% 2.84/1.00  --prep_def_merge_mbd                    true
% 2.84/1.00  --prep_def_merge_tr_red                 false
% 2.84/1.00  --prep_def_merge_tr_cl                  false
% 2.84/1.00  --smt_preprocessing                     true
% 2.84/1.00  --smt_ac_axioms                         fast
% 2.84/1.00  --preprocessed_out                      false
% 2.84/1.00  --preprocessed_stats                    false
% 2.84/1.00  
% 2.84/1.00  ------ Abstraction refinement Options
% 2.84/1.00  
% 2.84/1.00  --abstr_ref                             []
% 2.84/1.00  --abstr_ref_prep                        false
% 2.84/1.00  --abstr_ref_until_sat                   false
% 2.84/1.00  --abstr_ref_sig_restrict                funpre
% 2.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.00  --abstr_ref_under                       []
% 2.84/1.00  
% 2.84/1.00  ------ SAT Options
% 2.84/1.00  
% 2.84/1.00  --sat_mode                              false
% 2.84/1.00  --sat_fm_restart_options                ""
% 2.84/1.00  --sat_gr_def                            false
% 2.84/1.00  --sat_epr_types                         true
% 2.84/1.00  --sat_non_cyclic_types                  false
% 2.84/1.00  --sat_finite_models                     false
% 2.84/1.00  --sat_fm_lemmas                         false
% 2.84/1.00  --sat_fm_prep                           false
% 2.84/1.00  --sat_fm_uc_incr                        true
% 2.84/1.00  --sat_out_model                         small
% 2.84/1.00  --sat_out_clauses                       false
% 2.84/1.00  
% 2.84/1.00  ------ QBF Options
% 2.84/1.00  
% 2.84/1.00  --qbf_mode                              false
% 2.84/1.00  --qbf_elim_univ                         false
% 2.84/1.00  --qbf_dom_inst                          none
% 2.84/1.00  --qbf_dom_pre_inst                      false
% 2.84/1.00  --qbf_sk_in                             false
% 2.84/1.00  --qbf_pred_elim                         true
% 2.84/1.00  --qbf_split                             512
% 2.84/1.00  
% 2.84/1.00  ------ BMC1 Options
% 2.84/1.00  
% 2.84/1.00  --bmc1_incremental                      false
% 2.84/1.00  --bmc1_axioms                           reachable_all
% 2.84/1.00  --bmc1_min_bound                        0
% 2.84/1.00  --bmc1_max_bound                        -1
% 2.84/1.00  --bmc1_max_bound_default                -1
% 2.84/1.00  --bmc1_symbol_reachability              true
% 2.84/1.00  --bmc1_property_lemmas                  false
% 2.84/1.00  --bmc1_k_induction                      false
% 2.84/1.00  --bmc1_non_equiv_states                 false
% 2.84/1.00  --bmc1_deadlock                         false
% 2.84/1.00  --bmc1_ucm                              false
% 2.84/1.00  --bmc1_add_unsat_core                   none
% 2.84/1.00  --bmc1_unsat_core_children              false
% 2.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.00  --bmc1_out_stat                         full
% 2.84/1.00  --bmc1_ground_init                      false
% 2.84/1.00  --bmc1_pre_inst_next_state              false
% 2.84/1.00  --bmc1_pre_inst_state                   false
% 2.84/1.00  --bmc1_pre_inst_reach_state             false
% 2.84/1.00  --bmc1_out_unsat_core                   false
% 2.84/1.00  --bmc1_aig_witness_out                  false
% 2.84/1.00  --bmc1_verbose                          false
% 2.84/1.00  --bmc1_dump_clauses_tptp                false
% 2.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.00  --bmc1_dump_file                        -
% 2.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.00  --bmc1_ucm_extend_mode                  1
% 2.84/1.00  --bmc1_ucm_init_mode                    2
% 2.84/1.00  --bmc1_ucm_cone_mode                    none
% 2.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.00  --bmc1_ucm_relax_model                  4
% 2.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.00  --bmc1_ucm_layered_model                none
% 2.84/1.00  --bmc1_ucm_max_lemma_size               10
% 2.84/1.00  
% 2.84/1.00  ------ AIG Options
% 2.84/1.00  
% 2.84/1.00  --aig_mode                              false
% 2.84/1.00  
% 2.84/1.00  ------ Instantiation Options
% 2.84/1.00  
% 2.84/1.00  --instantiation_flag                    true
% 2.84/1.00  --inst_sos_flag                         false
% 2.84/1.00  --inst_sos_phase                        true
% 2.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel_side                     none
% 2.84/1.00  --inst_solver_per_active                1400
% 2.84/1.00  --inst_solver_calls_frac                1.
% 2.84/1.00  --inst_passive_queue_type               priority_queues
% 2.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.00  --inst_passive_queues_freq              [25;2]
% 2.84/1.00  --inst_dismatching                      true
% 2.84/1.00  --inst_eager_unprocessed_to_passive     true
% 2.84/1.00  --inst_prop_sim_given                   true
% 2.84/1.00  --inst_prop_sim_new                     false
% 2.84/1.00  --inst_subs_new                         false
% 2.84/1.00  --inst_eq_res_simp                      false
% 2.84/1.00  --inst_subs_given                       false
% 2.84/1.00  --inst_orphan_elimination               true
% 2.84/1.00  --inst_learning_loop_flag               true
% 2.84/1.00  --inst_learning_start                   3000
% 2.84/1.00  --inst_learning_factor                  2
% 2.84/1.00  --inst_start_prop_sim_after_learn       3
% 2.84/1.00  --inst_sel_renew                        solver
% 2.84/1.00  --inst_lit_activity_flag                true
% 2.84/1.00  --inst_restr_to_given                   false
% 2.84/1.00  --inst_activity_threshold               500
% 2.84/1.00  --inst_out_proof                        true
% 2.84/1.00  
% 2.84/1.00  ------ Resolution Options
% 2.84/1.00  
% 2.84/1.00  --resolution_flag                       false
% 2.84/1.00  --res_lit_sel                           adaptive
% 2.84/1.00  --res_lit_sel_side                      none
% 2.84/1.00  --res_ordering                          kbo
% 2.84/1.00  --res_to_prop_solver                    active
% 2.84/1.00  --res_prop_simpl_new                    false
% 2.84/1.00  --res_prop_simpl_given                  true
% 2.84/1.00  --res_passive_queue_type                priority_queues
% 2.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.00  --res_passive_queues_freq               [15;5]
% 2.84/1.00  --res_forward_subs                      full
% 2.84/1.00  --res_backward_subs                     full
% 2.84/1.00  --res_forward_subs_resolution           true
% 2.84/1.00  --res_backward_subs_resolution          true
% 2.84/1.00  --res_orphan_elimination                true
% 2.84/1.00  --res_time_limit                        2.
% 2.84/1.00  --res_out_proof                         true
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Options
% 2.84/1.00  
% 2.84/1.00  --superposition_flag                    true
% 2.84/1.00  --sup_passive_queue_type                priority_queues
% 2.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.00  --demod_completeness_check              fast
% 2.84/1.00  --demod_use_ground                      true
% 2.84/1.00  --sup_to_prop_solver                    passive
% 2.84/1.00  --sup_prop_simpl_new                    true
% 2.84/1.00  --sup_prop_simpl_given                  true
% 2.84/1.00  --sup_fun_splitting                     false
% 2.84/1.00  --sup_smt_interval                      50000
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Simplification Setup
% 2.84/1.00  
% 2.84/1.00  --sup_indices_passive                   []
% 2.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_full_bw                           [BwDemod]
% 2.84/1.00  --sup_immed_triv                        [TrivRules]
% 2.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_immed_bw_main                     []
% 2.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  
% 2.84/1.00  ------ Combination Options
% 2.84/1.00  
% 2.84/1.00  --comb_res_mult                         3
% 2.84/1.00  --comb_sup_mult                         2
% 2.84/1.00  --comb_inst_mult                        10
% 2.84/1.00  
% 2.84/1.00  ------ Debug Options
% 2.84/1.00  
% 2.84/1.00  --dbg_backtrace                         false
% 2.84/1.00  --dbg_dump_prop_clauses                 false
% 2.84/1.00  --dbg_dump_prop_clauses_file            -
% 2.84/1.00  --dbg_out_stat                          false
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  ------ Proving...
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  % SZS status Theorem for theBenchmark.p
% 2.84/1.00  
% 2.84/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.84/1.00  
% 2.84/1.00  fof(f11,conjecture,(
% 2.84/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f12,negated_conjecture,(
% 2.84/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.84/1.00    inference(negated_conjecture,[],[f11])).
% 2.84/1.00  
% 2.84/1.00  fof(f25,plain,(
% 2.84/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.84/1.00    inference(ennf_transformation,[],[f12])).
% 2.84/1.00  
% 2.84/1.00  fof(f26,plain,(
% 2.84/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.84/1.00    inference(flattening,[],[f25])).
% 2.84/1.00  
% 2.84/1.00  fof(f31,plain,(
% 2.84/1.00    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.84/1.00    inference(nnf_transformation,[],[f26])).
% 2.84/1.00  
% 2.84/1.00  fof(f32,plain,(
% 2.84/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.84/1.00    inference(flattening,[],[f31])).
% 2.84/1.00  
% 2.84/1.00  fof(f33,plain,(
% 2.84/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.84/1.00    inference(rectify,[],[f32])).
% 2.84/1.00  
% 2.84/1.00  fof(f36,plain,(
% 2.84/1.00    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK3 & v3_pre_topc(sK3,X0) & r1_tarski(sK3,X1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.84/1.00    introduced(choice_axiom,[])).
% 2.84/1.00  
% 2.84/1.00  fof(f35,plain,(
% 2.84/1.00    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK2,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.84/1.00    introduced(choice_axiom,[])).
% 2.84/1.00  
% 2.84/1.00  fof(f34,plain,(
% 2.84/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK1) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) | ~v2_tops_1(X1,sK1)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_1(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.84/1.00    introduced(choice_axiom,[])).
% 2.84/1.00  
% 2.84/1.00  fof(f37,plain,(
% 2.84/1.00    (((k1_xboole_0 != sK3 & v3_pre_topc(sK3,sK1) & r1_tarski(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~v2_tops_1(sK2,sK1)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_1(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).
% 2.84/1.00  
% 2.84/1.00  fof(f55,plain,(
% 2.84/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.84/1.00    inference(cnf_transformation,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  fof(f57,plain,(
% 2.84/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_tops_1(sK2,sK1)),
% 2.84/1.00    inference(cnf_transformation,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  fof(f9,axiom,(
% 2.84/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f22,plain,(
% 2.84/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.84/1.00    inference(ennf_transformation,[],[f9])).
% 2.84/1.00  
% 2.84/1.00  fof(f23,plain,(
% 2.84/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.84/1.00    inference(flattening,[],[f22])).
% 2.84/1.00  
% 2.84/1.00  fof(f49,plain,(
% 2.84/1.00    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f23])).
% 2.84/1.00  
% 2.84/1.00  fof(f53,plain,(
% 2.84/1.00    v2_pre_topc(sK1)),
% 2.84/1.00    inference(cnf_transformation,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  fof(f54,plain,(
% 2.84/1.00    l1_pre_topc(sK1)),
% 2.84/1.00    inference(cnf_transformation,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  fof(f50,plain,(
% 2.84/1.00    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f23])).
% 2.84/1.00  
% 2.84/1.00  fof(f10,axiom,(
% 2.84/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f24,plain,(
% 2.84/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/1.00    inference(ennf_transformation,[],[f10])).
% 2.84/1.00  
% 2.84/1.00  fof(f30,plain,(
% 2.84/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/1.00    inference(nnf_transformation,[],[f24])).
% 2.84/1.00  
% 2.84/1.00  fof(f52,plain,(
% 2.84/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f30])).
% 2.84/1.00  
% 2.84/1.00  fof(f59,plain,(
% 2.84/1.00    v3_pre_topc(sK3,sK1) | ~v2_tops_1(sK2,sK1)),
% 2.84/1.00    inference(cnf_transformation,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  fof(f51,plain,(
% 2.84/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f30])).
% 2.84/1.00  
% 2.84/1.00  fof(f6,axiom,(
% 2.84/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f17,plain,(
% 2.84/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.84/1.00    inference(ennf_transformation,[],[f6])).
% 2.84/1.00  
% 2.84/1.00  fof(f18,plain,(
% 2.84/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.84/1.00    inference(flattening,[],[f17])).
% 2.84/1.00  
% 2.84/1.00  fof(f46,plain,(
% 2.84/1.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f18])).
% 2.84/1.00  
% 2.84/1.00  fof(f7,axiom,(
% 2.84/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f19,plain,(
% 2.84/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/1.00    inference(ennf_transformation,[],[f7])).
% 2.84/1.00  
% 2.84/1.00  fof(f47,plain,(
% 2.84/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f19])).
% 2.84/1.00  
% 2.84/1.00  fof(f3,axiom,(
% 2.84/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f27,plain,(
% 2.84/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.84/1.00    inference(nnf_transformation,[],[f3])).
% 2.84/1.00  
% 2.84/1.00  fof(f40,plain,(
% 2.84/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.84/1.00    inference(cnf_transformation,[],[f27])).
% 2.84/1.00  
% 2.84/1.00  fof(f1,axiom,(
% 2.84/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f13,plain,(
% 2.84/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.84/1.00    inference(ennf_transformation,[],[f1])).
% 2.84/1.00  
% 2.84/1.00  fof(f14,plain,(
% 2.84/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.84/1.00    inference(flattening,[],[f13])).
% 2.84/1.00  
% 2.84/1.00  fof(f38,plain,(
% 2.84/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f14])).
% 2.84/1.00  
% 2.84/1.00  fof(f56,plain,(
% 2.84/1.00    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | v2_tops_1(sK2,sK1)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  fof(f41,plain,(
% 2.84/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f27])).
% 2.84/1.00  
% 2.84/1.00  fof(f8,axiom,(
% 2.84/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f20,plain,(
% 2.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/1.00    inference(ennf_transformation,[],[f8])).
% 2.84/1.00  
% 2.84/1.00  fof(f21,plain,(
% 2.84/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/1.00    inference(flattening,[],[f20])).
% 2.84/1.00  
% 2.84/1.00  fof(f48,plain,(
% 2.84/1.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f21])).
% 2.84/1.00  
% 2.84/1.00  fof(f58,plain,(
% 2.84/1.00    r1_tarski(sK3,sK2) | ~v2_tops_1(sK2,sK1)),
% 2.84/1.00    inference(cnf_transformation,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  fof(f2,axiom,(
% 2.84/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f39,plain,(
% 2.84/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f2])).
% 2.84/1.00  
% 2.84/1.00  fof(f4,axiom,(
% 2.84/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f15,plain,(
% 2.84/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.84/1.00    inference(ennf_transformation,[],[f4])).
% 2.84/1.00  
% 2.84/1.00  fof(f42,plain,(
% 2.84/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f15])).
% 2.84/1.00  
% 2.84/1.00  fof(f5,axiom,(
% 2.84/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f16,plain,(
% 2.84/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.84/1.00    inference(ennf_transformation,[],[f5])).
% 2.84/1.00  
% 2.84/1.00  fof(f28,plain,(
% 2.84/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.84/1.00    introduced(choice_axiom,[])).
% 2.84/1.00  
% 2.84/1.00  fof(f29,plain,(
% 2.84/1.00    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).
% 2.84/1.00  
% 2.84/1.00  fof(f43,plain,(
% 2.84/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.84/1.00    inference(cnf_transformation,[],[f29])).
% 2.84/1.00  
% 2.84/1.00  fof(f60,plain,(
% 2.84/1.00    k1_xboole_0 != sK3 | ~v2_tops_1(sK2,sK1)),
% 2.84/1.00    inference(cnf_transformation,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  cnf(c_20,negated_conjecture,
% 2.84/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.84/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1805,plain,
% 2.84/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_18,negated_conjecture,
% 2.84/1.00      ( ~ v2_tops_1(sK2,sK1)
% 2.84/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.84/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1807,plain,
% 2.84/1.00      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.84/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_12,plain,
% 2.84/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ v2_pre_topc(X3)
% 2.84/1.00      | ~ l1_pre_topc(X3)
% 2.84/1.00      | ~ l1_pre_topc(X1)
% 2.84/1.00      | k1_tops_1(X1,X0) = X0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_22,negated_conjecture,
% 2.84/1.00      ( v2_pre_topc(sK1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_389,plain,
% 2.84/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.84/1.00      | ~ l1_pre_topc(X1)
% 2.84/1.00      | ~ l1_pre_topc(X3)
% 2.84/1.00      | k1_tops_1(X1,X0) = X0
% 2.84/1.00      | sK1 != X3 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_390,plain,
% 2.84/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ l1_pre_topc(X1)
% 2.84/1.00      | ~ l1_pre_topc(sK1)
% 2.84/1.00      | k1_tops_1(X1,X0) = X0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_389]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_21,negated_conjecture,
% 2.84/1.00      ( l1_pre_topc(sK1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_394,plain,
% 2.84/1.00      ( ~ l1_pre_topc(X1)
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ v3_pre_topc(X0,X1)
% 2.84/1.00      | k1_tops_1(X1,X0) = X0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_390,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_395,plain,
% 2.84/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ l1_pre_topc(X1)
% 2.84/1.00      | k1_tops_1(X1,X0) = X0 ),
% 2.84/1.00      inference(renaming,[status(thm)],[c_394]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_429,plain,
% 2.84/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(X1,X0) = X0
% 2.84/1.00      | sK1 != X1 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_395,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_430,plain,
% 2.84/1.00      ( ~ v3_pre_topc(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) = X0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_429]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1295,plain,
% 2.84/1.00      ( ~ v3_pre_topc(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) = X0
% 2.84/1.00      | ~ sP2_iProver_split ),
% 2.84/1.00      inference(splitting,
% 2.84/1.00                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.84/1.00                [c_430]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1801,plain,
% 2.84/1.00      ( k1_tops_1(sK1,X0) = X0
% 2.84/1.00      | v3_pre_topc(X0,sK1) != iProver_top
% 2.84/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | sP2_iProver_split != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1295]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1296,plain,
% 2.84/1.00      ( sP2_iProver_split | sP0_iProver_split ),
% 2.84/1.00      inference(splitting,
% 2.84/1.00                [splitting(split),new_symbols(definition,[])],
% 2.84/1.00                [c_430]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1327,plain,
% 2.84/1.00      ( sP2_iProver_split = iProver_top
% 2.84/1.00      | sP0_iProver_split = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1328,plain,
% 2.84/1.00      ( k1_tops_1(sK1,X0) = X0
% 2.84/1.00      | v3_pre_topc(X0,sK1) != iProver_top
% 2.84/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | sP2_iProver_split != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1295]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_11,plain,
% 2.84/1.00      ( v3_pre_topc(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.84/1.00      | ~ v2_pre_topc(X1)
% 2.84/1.00      | ~ l1_pre_topc(X1)
% 2.84/1.00      | ~ l1_pre_topc(X3)
% 2.84/1.00      | k1_tops_1(X1,X0) != X0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_364,plain,
% 2.84/1.00      ( v3_pre_topc(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.84/1.00      | ~ l1_pre_topc(X1)
% 2.84/1.00      | ~ l1_pre_topc(X3)
% 2.84/1.00      | k1_tops_1(X1,X0) != X0
% 2.84/1.00      | sK1 != X1 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_365,plain,
% 2.84/1.00      ( v3_pre_topc(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ l1_pre_topc(X2)
% 2.84/1.00      | ~ l1_pre_topc(sK1)
% 2.84/1.00      | k1_tops_1(sK1,X0) != X0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_364]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_369,plain,
% 2.84/1.00      ( ~ l1_pre_topc(X2)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/1.00      | v3_pre_topc(X0,sK1)
% 2.84/1.00      | k1_tops_1(sK1,X0) != X0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_365,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_370,plain,
% 2.84/1.00      ( v3_pre_topc(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ l1_pre_topc(X2)
% 2.84/1.00      | k1_tops_1(sK1,X0) != X0 ),
% 2.84/1.00      inference(renaming,[status(thm)],[c_369]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_507,plain,
% 2.84/1.00      ( v3_pre_topc(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) != X0
% 2.84/1.00      | sK1 != X2 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_370,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_508,plain,
% 2.84/1.00      ( v3_pre_topc(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) != X0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_507]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1292,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ sP0_iProver_split ),
% 2.84/1.00      inference(splitting,
% 2.84/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.84/1.00                [c_508]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1795,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | sP0_iProver_split != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1292]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2173,plain,
% 2.84/1.00      ( sP0_iProver_split != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1805,c_1795]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3088,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | v3_pre_topc(X0,sK1) != iProver_top
% 2.84/1.00      | k1_tops_1(sK1,X0) = X0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_1801,c_1327,c_1328,c_2173]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3089,plain,
% 2.84/1.00      ( k1_tops_1(sK1,X0) = X0
% 2.84/1.00      | v3_pre_topc(X0,sK1) != iProver_top
% 2.84/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.84/1.00      inference(renaming,[status(thm)],[c_3088]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3096,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK3) = sK3
% 2.84/1.00      | v2_tops_1(sK2,sK1) != iProver_top
% 2.84/1.00      | v3_pre_topc(sK3,sK1) != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1807,c_3089]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_13,plain,
% 2.84/1.00      ( v2_tops_1(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ l1_pre_topc(X1)
% 2.84/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_462,plain,
% 2.84/1.00      ( v2_tops_1(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.84/1.00      | sK1 != X1 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_463,plain,
% 2.84/1.00      ( v2_tops_1(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_462]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_763,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0
% 2.84/1.00      | sK1 != sK1
% 2.84/1.00      | sK2 != X0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_463]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_764,plain,
% 2.84/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_763]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_766,plain,
% 2.84/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_764,c_20]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_16,negated_conjecture,
% 2.84/1.00      ( ~ v2_tops_1(sK2,sK1) | v3_pre_topc(sK3,sK1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_791,plain,
% 2.84/1.00      ( v3_pre_topc(sK3,sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0
% 2.84/1.00      | sK1 != sK1
% 2.84/1.00      | sK2 != X0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_463]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_792,plain,
% 2.84/1.00      ( v3_pre_topc(sK3,sK1)
% 2.84/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_791]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_794,plain,
% 2.84/1.00      ( v3_pre_topc(sK3,sK1) | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_792,c_20]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1385,plain,
% 2.84/1.00      ( k1_tops_1(sK1,X0) = X0
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ v3_pre_topc(X0,sK1) ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_1295,c_1292,c_1296]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1386,plain,
% 2.84/1.00      ( ~ v3_pre_topc(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) = X0 ),
% 2.84/1.00      inference(renaming,[status(thm)],[c_1385]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2665,plain,
% 2.84/1.00      ( ~ v3_pre_topc(sK3,sK1)
% 2.84/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,sK3) = sK3 ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_1386]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_14,plain,
% 2.84/1.00      ( ~ v2_tops_1(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ l1_pre_topc(X1)
% 2.84/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_447,plain,
% 2.84/1.00      ( ~ v2_tops_1(X0,X1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.84/1.00      | sK1 != X1 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_448,plain,
% 2.84/1.00      ( ~ v2_tops_1(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) = k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_447]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1799,plain,
% 2.84/1.00      ( k1_tops_1(sK1,X0) = k1_xboole_0
% 2.84/1.00      | v2_tops_1(X0,sK1) != iProver_top
% 2.84/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2937,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 2.84/1.00      | v2_tops_1(sK2,sK1) != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1805,c_1799]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_8,plain,
% 2.84/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.84/1.00      | ~ v2_pre_topc(X0)
% 2.84/1.00      | ~ l1_pre_topc(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_346,plain,
% 2.84/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.84/1.00      | ~ l1_pre_topc(X0)
% 2.84/1.00      | sK1 != X0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_347,plain,
% 2.84/1.00      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ l1_pre_topc(sK1) ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_346]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_351,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_347,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_352,plain,
% 2.84/1.00      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.84/1.00      inference(renaming,[status(thm)],[c_351]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1970,plain,
% 2.84/1.00      ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
% 2.84/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_352]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_9,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.84/1.00      | ~ l1_pre_topc(X1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_495,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.84/1.00      | sK1 != X1 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_496,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_495]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1976,plain,
% 2.84/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_496]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1997,plain,
% 2.84/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | r1_tarski(sK2,u1_struct_0(sK1)) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1299,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2049,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK2) != X0
% 2.84/1.00      | k1_tops_1(sK1,sK2) = k1_xboole_0
% 2.84/1.00      | k1_xboole_0 != X0 ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_1299]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2208,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK2) != k1_tops_1(sK1,sK2)
% 2.84/1.00      | k1_tops_1(sK1,sK2) = k1_xboole_0
% 2.84/1.00      | k1_xboole_0 != k1_tops_1(sK1,sK2) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_2049]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1298,plain,( X0 = X0 ),theory(equality) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2209,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK2) = k1_tops_1(sK1,sK2) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_1298]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_0,plain,
% 2.84/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2073,plain,
% 2.84/1.00      ( r1_tarski(X0,u1_struct_0(sK1))
% 2.84/1.00      | ~ r1_tarski(X0,sK2)
% 2.84/1.00      | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2239,plain,
% 2.84/1.00      ( r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1))
% 2.84/1.00      | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
% 2.84/1.00      | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_2073]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_19,negated_conjecture,
% 2.84/1.00      ( v2_tops_1(sK2,sK1)
% 2.84/1.00      | ~ v3_pre_topc(X0,sK1)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ r1_tarski(X0,sK2)
% 2.84/1.00      | k1_xboole_0 = X0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2301,plain,
% 2.84/1.00      ( v2_tops_1(sK2,sK1)
% 2.84/1.00      | ~ v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
% 2.84/1.00      | ~ m1_subset_1(k1_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
% 2.84/1.00      | k1_xboole_0 = k1_tops_1(sK1,sK2) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2482,plain,
% 2.84/1.00      ( m1_subset_1(k1_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2958,plain,
% 2.84/1.00      ( ~ v2_tops_1(sK2,sK1) | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 2.84/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2937]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2992,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_2937,c_20,c_1970,c_1976,c_1997,c_2208,c_2209,c_2239,
% 2.84/1.00                 c_2301,c_2482,c_2958]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3159,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK3) = sK3 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_3096,c_20,c_766,c_794,c_1970,c_1976,c_1997,c_2208,
% 2.84/1.00                 c_2209,c_2239,c_2301,c_2482,c_2665,c_2958]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_10,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ r1_tarski(X0,X2)
% 2.84/1.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.84/1.00      | ~ l1_pre_topc(X1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_477,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/1.00      | ~ r1_tarski(X0,X2)
% 2.84/1.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 2.84/1.00      | sK1 != X1 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_478,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | ~ r1_tarski(X0,X1)
% 2.84/1.00      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1797,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.84/1.00      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3191,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | r1_tarski(sK3,X0) != iProver_top
% 2.84/1.00      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_3159,c_1797]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_768,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK2) != k1_xboole_0
% 2.84/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4379,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.84/1.00      | r1_tarski(sK3,X0) != iProver_top
% 2.84/1.00      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_3191,c_20,c_768,c_1970,c_1976,c_1997,c_2208,c_2209,
% 2.84/1.00                 c_2239,c_2301,c_2482,c_2958]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4390,plain,
% 2.84/1.00      ( r1_tarski(sK3,k1_tops_1(sK1,sK2)) = iProver_top
% 2.84/1.00      | r1_tarski(sK3,sK2) != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1805,c_4379]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4393,plain,
% 2.84/1.00      ( r1_tarski(sK3,sK2) != iProver_top
% 2.84/1.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.84/1.00      inference(light_normalisation,[status(thm)],[c_4390,c_2992]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_17,negated_conjecture,
% 2.84/1.00      ( ~ v2_tops_1(sK2,sK1) | r1_tarski(sK3,sK2) ),
% 2.84/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_777,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | r1_tarski(sK3,sK2)
% 2.84/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0
% 2.84/1.00      | sK1 != sK1
% 2.84/1.00      | sK2 != X0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_463]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_778,plain,
% 2.84/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | r1_tarski(sK3,sK2)
% 2.84/1.00      | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_777]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_780,plain,
% 2.84/1.00      ( r1_tarski(sK3,sK2) | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_778,c_20]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_782,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK2) != k1_xboole_0
% 2.84/1.00      | r1_tarski(sK3,sK2) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4822,plain,
% 2.84/1.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_4393,c_20,c_782,c_1970,c_1976,c_1997,c_2208,c_2209,
% 2.84/1.00                 c_2239,c_2301,c_2482,c_2958]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1,plain,
% 2.84/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1813,plain,
% 2.84/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1814,plain,
% 2.84/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.84/1.00      | r1_tarski(X2,X0) != iProver_top
% 2.84/1.00      | r1_tarski(X2,X1) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2380,plain,
% 2.84/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.84/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1813,c_1814]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4830,plain,
% 2.84/1.00      ( r1_tarski(sK3,X0) = iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_4822,c_2380]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4,plain,
% 2.84/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_7,plain,
% 2.84/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_327,plain,
% 2.84/1.00      ( ~ r1_tarski(X0,X1)
% 2.84/1.00      | X2 != X0
% 2.84/1.00      | sK0(X2) != X1
% 2.84/1.00      | k1_xboole_0 = X2 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_328,plain,
% 2.84/1.00      ( ~ r1_tarski(X0,sK0(X0)) | k1_xboole_0 = X0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_327]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1804,plain,
% 2.84/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,sK0(X0)) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_6093,plain,
% 2.84/1.00      ( sK3 = k1_xboole_0 ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_4830,c_1804]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_15,negated_conjecture,
% 2.84/1.00      ( ~ v2_tops_1(sK2,sK1) | k1_xboole_0 != sK3 ),
% 2.84/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_805,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0
% 2.84/1.00      | sK1 != sK1
% 2.84/1.00      | sK2 != X0
% 2.84/1.00      | sK3 != k1_xboole_0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_463]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_806,plain,
% 2.84/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.84/1.00      | k1_tops_1(sK1,sK2) != k1_xboole_0
% 2.84/1.00      | sK3 != k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_805]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_808,plain,
% 2.84/1.00      ( k1_tops_1(sK1,sK2) != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_806,c_20]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(contradiction,plain,
% 2.84/1.00      ( $false ),
% 2.84/1.00      inference(minisat,[status(thm)],[c_6093,c_2992,c_808]) ).
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.84/1.00  
% 2.84/1.00  ------                               Statistics
% 2.84/1.00  
% 2.84/1.00  ------ General
% 2.84/1.00  
% 2.84/1.00  abstr_ref_over_cycles:                  0
% 2.84/1.00  abstr_ref_under_cycles:                 0
% 2.84/1.00  gc_basic_clause_elim:                   0
% 2.84/1.00  forced_gc_time:                         0
% 2.84/1.00  parsing_time:                           0.007
% 2.84/1.00  unif_index_cands_time:                  0.
% 2.84/1.00  unif_index_add_time:                    0.
% 2.84/1.00  orderings_time:                         0.
% 2.84/1.00  out_proof_time:                         0.016
% 2.84/1.00  total_time:                             0.189
% 2.84/1.00  num_of_symbols:                         50
% 2.84/1.00  num_of_terms:                           2642
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing
% 2.84/1.00  
% 2.84/1.00  num_of_splits:                          4
% 2.84/1.00  num_of_split_atoms:                     3
% 2.84/1.00  num_of_reused_defs:                     1
% 2.84/1.00  num_eq_ax_congr_red:                    16
% 2.84/1.00  num_of_sem_filtered_clauses:            4
% 2.84/1.00  num_of_subtypes:                        0
% 2.84/1.00  monotx_restored_types:                  0
% 2.84/1.00  sat_num_of_epr_types:                   0
% 2.84/1.00  sat_num_of_non_cyclic_types:            0
% 2.84/1.00  sat_guarded_non_collapsed_types:        0
% 2.84/1.00  num_pure_diseq_elim:                    0
% 2.84/1.00  simp_replaced_by:                       0
% 2.84/1.00  res_preprocessed:                       107
% 2.84/1.00  prep_upred:                             0
% 2.84/1.00  prep_unflattend:                        33
% 2.84/1.00  smt_new_axioms:                         0
% 2.84/1.00  pred_elim_cands:                        4
% 2.84/1.00  pred_elim:                              3
% 2.84/1.00  pred_elim_cl:                           3
% 2.84/1.00  pred_elim_cycles:                       7
% 2.84/1.00  merged_defs:                            8
% 2.84/1.00  merged_defs_ncl:                        0
% 2.84/1.00  bin_hyper_res:                          8
% 2.84/1.00  prep_cycles:                            4
% 2.84/1.00  pred_elim_time:                         0.015
% 2.84/1.00  splitting_time:                         0.
% 2.84/1.00  sem_filter_time:                        0.
% 2.84/1.00  monotx_time:                            0.001
% 2.84/1.00  subtype_inf_time:                       0.
% 2.84/1.00  
% 2.84/1.00  ------ Problem properties
% 2.84/1.00  
% 2.84/1.00  clauses:                                24
% 2.84/1.00  conjectures:                            6
% 2.84/1.00  epr:                                    7
% 2.84/1.00  horn:                                   21
% 2.84/1.00  ground:                                 7
% 2.84/1.00  unary:                                  2
% 2.84/1.00  binary:                                 15
% 2.84/1.00  lits:                                   58
% 2.84/1.00  lits_eq:                                11
% 2.84/1.00  fd_pure:                                0
% 2.84/1.00  fd_pseudo:                              0
% 2.84/1.00  fd_cond:                                4
% 2.84/1.00  fd_pseudo_cond:                         0
% 2.84/1.00  ac_symbols:                             0
% 2.84/1.00  
% 2.84/1.00  ------ Propositional Solver
% 2.84/1.00  
% 2.84/1.00  prop_solver_calls:                      30
% 2.84/1.00  prop_fast_solver_calls:                 1026
% 2.84/1.00  smt_solver_calls:                       0
% 2.84/1.00  smt_fast_solver_calls:                  0
% 2.84/1.00  prop_num_of_clauses:                    1822
% 2.84/1.00  prop_preprocess_simplified:             5837
% 2.84/1.00  prop_fo_subsumed:                       55
% 2.84/1.00  prop_solver_time:                       0.
% 2.84/1.00  smt_solver_time:                        0.
% 2.84/1.00  smt_fast_solver_time:                   0.
% 2.84/1.00  prop_fast_solver_time:                  0.
% 2.84/1.00  prop_unsat_core_time:                   0.
% 2.84/1.00  
% 2.84/1.00  ------ QBF
% 2.84/1.00  
% 2.84/1.00  qbf_q_res:                              0
% 2.84/1.00  qbf_num_tautologies:                    0
% 2.84/1.00  qbf_prep_cycles:                        0
% 2.84/1.00  
% 2.84/1.00  ------ BMC1
% 2.84/1.00  
% 2.84/1.00  bmc1_current_bound:                     -1
% 2.84/1.00  bmc1_last_solved_bound:                 -1
% 2.84/1.00  bmc1_unsat_core_size:                   -1
% 2.84/1.00  bmc1_unsat_core_parents_size:           -1
% 2.84/1.00  bmc1_merge_next_fun:                    0
% 2.84/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.84/1.00  
% 2.84/1.00  ------ Instantiation
% 2.84/1.00  
% 2.84/1.00  inst_num_of_clauses:                    581
% 2.84/1.00  inst_num_in_passive:                    221
% 2.84/1.00  inst_num_in_active:                     346
% 2.84/1.00  inst_num_in_unprocessed:                14
% 2.84/1.00  inst_num_of_loops:                      380
% 2.84/1.00  inst_num_of_learning_restarts:          0
% 2.84/1.00  inst_num_moves_active_passive:          30
% 2.84/1.00  inst_lit_activity:                      0
% 2.84/1.00  inst_lit_activity_moves:                0
% 2.84/1.00  inst_num_tautologies:                   0
% 2.84/1.00  inst_num_prop_implied:                  0
% 2.84/1.00  inst_num_existing_simplified:           0
% 2.84/1.00  inst_num_eq_res_simplified:             0
% 2.84/1.00  inst_num_child_elim:                    0
% 2.84/1.00  inst_num_of_dismatching_blockings:      112
% 2.84/1.00  inst_num_of_non_proper_insts:           543
% 2.84/1.00  inst_num_of_duplicates:                 0
% 2.84/1.00  inst_inst_num_from_inst_to_res:         0
% 2.84/1.00  inst_dismatching_checking_time:         0.
% 2.84/1.00  
% 2.84/1.00  ------ Resolution
% 2.84/1.00  
% 2.84/1.00  res_num_of_clauses:                     0
% 2.84/1.00  res_num_in_passive:                     0
% 2.84/1.00  res_num_in_active:                      0
% 2.84/1.00  res_num_of_loops:                       111
% 2.84/1.00  res_forward_subset_subsumed:            79
% 2.84/1.00  res_backward_subset_subsumed:           0
% 2.84/1.00  res_forward_subsumed:                   0
% 2.84/1.00  res_backward_subsumed:                  0
% 2.84/1.00  res_forward_subsumption_resolution:     0
% 2.84/1.00  res_backward_subsumption_resolution:    0
% 2.84/1.00  res_clause_to_clause_subsumption:       696
% 2.84/1.00  res_orphan_elimination:                 0
% 2.84/1.00  res_tautology_del:                      118
% 2.84/1.00  res_num_eq_res_simplified:              0
% 2.84/1.00  res_num_sel_changes:                    0
% 2.84/1.00  res_moves_from_active_to_pass:          0
% 2.84/1.00  
% 2.84/1.00  ------ Superposition
% 2.84/1.00  
% 2.84/1.00  sup_time_total:                         0.
% 2.84/1.00  sup_time_generating:                    0.
% 2.84/1.00  sup_time_sim_full:                      0.
% 2.84/1.00  sup_time_sim_immed:                     0.
% 2.84/1.00  
% 2.84/1.00  sup_num_of_clauses:                     93
% 2.84/1.00  sup_num_in_active:                      65
% 2.84/1.00  sup_num_in_passive:                     28
% 2.84/1.00  sup_num_of_loops:                       75
% 2.84/1.00  sup_fw_superposition:                   122
% 2.84/1.00  sup_bw_superposition:                   55
% 2.84/1.00  sup_immediate_simplified:               72
% 2.84/1.00  sup_given_eliminated:                   4
% 2.84/1.00  comparisons_done:                       0
% 2.84/1.00  comparisons_avoided:                    0
% 2.84/1.00  
% 2.84/1.00  ------ Simplifications
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  sim_fw_subset_subsumed:                 32
% 2.84/1.00  sim_bw_subset_subsumed:                 3
% 2.84/1.00  sim_fw_subsumed:                        27
% 2.84/1.00  sim_bw_subsumed:                        3
% 2.84/1.00  sim_fw_subsumption_res:                 1
% 2.84/1.00  sim_bw_subsumption_res:                 0
% 2.84/1.00  sim_tautology_del:                      17
% 2.84/1.00  sim_eq_tautology_del:                   1
% 2.84/1.00  sim_eq_res_simp:                        0
% 2.84/1.00  sim_fw_demodulated:                     0
% 2.84/1.00  sim_bw_demodulated:                     8
% 2.84/1.00  sim_light_normalised:                   24
% 2.84/1.00  sim_joinable_taut:                      0
% 2.84/1.00  sim_joinable_simp:                      0
% 2.84/1.00  sim_ac_normalised:                      0
% 2.84/1.00  sim_smt_subsumption:                    0
% 2.84/1.00  
%------------------------------------------------------------------------------

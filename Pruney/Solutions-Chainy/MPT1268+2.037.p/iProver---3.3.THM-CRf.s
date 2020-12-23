%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:09 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  138 (1328 expanded)
%              Number of clauses        :   81 ( 321 expanded)
%              Number of leaves         :   17 ( 336 expanded)
%              Depth                    :   21
%              Number of atoms          :  565 (11484 expanded)
%              Number of equality atoms :  138 (1886 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).

fof(f59,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK2)
      | ~ r1_tarski(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tops_1(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,
    ( r1_tarski(sK4,sK3)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,
    ( k1_xboole_0 != sK4
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1917,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1908,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_411,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_412,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_414,plain,
    ( r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r2_hidden(X2,X0)
    | ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_21])).

cnf(c_415,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X1)) ),
    inference(renaming,[status(thm)],[c_414])).

cnf(c_1900,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_2873,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1900])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_478,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_479,plain,
    ( v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_479])).

cnf(c_776,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_778,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_20])).

cnf(c_780,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | v3_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_803,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_479])).

cnf(c_804,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_803])).

cnf(c_806,plain,
    ( v3_pre_topc(sK4,sK2)
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_804,c_20])).

cnf(c_808,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | v3_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_2716,plain,
    ( ~ v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK4,X0)
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ r2_hidden(X1,sK4) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_2717,plain,
    ( v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2716])).

cnf(c_1906,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_463,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_464,plain,
    ( ~ v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_1899,plain,
    ( k1_tops_1(sK2,X0) = k1_xboole_0
    | v2_tops_1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_2801,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1899])).

cnf(c_6,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_330,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_331,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_21])).

cnf(c_336,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_335])).

cnf(c_2073,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_2079,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2112,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1376,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2171,plain,
    ( k1_tops_1(sK2,sK3) != X0
    | k1_tops_1(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_2320,plain,
    ( k1_tops_1(sK2,sK3) != k1_tops_1(sK2,sK3)
    | k1_tops_1(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_1375,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2321,plain,
    ( k1_tops_1(sK2,sK3) = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2190,plain,
    ( r1_tarski(X0,u1_struct_0(sK2))
    | ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2337,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_19,negated_conjecture,
    ( v2_tops_1(sK3,sK2)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2382,plain,
    ( v2_tops_1(sK3,sK2)
    | ~ v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
    | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | k1_xboole_0 = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2589,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2813,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | k1_tops_1(sK2,sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2801])).

cnf(c_2855,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2801,c_20,c_2073,c_2079,c_2112,c_2320,c_2321,c_2337,c_2382,c_2589,c_2813])).

cnf(c_3610,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2873,c_20,c_780,c_808,c_2073,c_2079,c_2112,c_2320,c_2321,c_2337,c_2382,c_2589,c_2717,c_2813])).

cnf(c_3621,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r1_tarski(sK4,sK4) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_3610])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_69,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_789,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,sK3)
    | k1_tops_1(sK2,X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_479])).

cnf(c_790,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,sK3)
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_792,plain,
    ( r1_tarski(sK4,sK3)
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_20])).

cnf(c_794,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2121,plain,
    ( ~ r1_tarski(k1_xboole_0,X0)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2122,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2121])).

cnf(c_3622,plain,
    ( r1_tarski(sK4,sK3) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_3610])).

cnf(c_3637,plain,
    ( r1_tarski(sK4,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3622,c_2855])).

cnf(c_3901,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3621,c_20,c_69,c_794,c_2073,c_2079,c_2112,c_2122,c_2320,c_2321,c_2337,c_2382,c_2589,c_2813,c_3637])).

cnf(c_3908,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1917,c_3901])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_479])).

cnf(c_818,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_820,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_818,c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3908,c_2855,c_820])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:57:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.11/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/1.00  
% 2.11/1.00  ------  iProver source info
% 2.11/1.00  
% 2.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/1.00  git: non_committed_changes: false
% 2.11/1.00  git: last_make_outside_of_git: false
% 2.11/1.00  
% 2.11/1.00  ------ 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options
% 2.11/1.00  
% 2.11/1.00  --out_options                           all
% 2.11/1.00  --tptp_safe_out                         true
% 2.11/1.00  --problem_path                          ""
% 2.11/1.00  --include_path                          ""
% 2.11/1.00  --clausifier                            res/vclausify_rel
% 2.11/1.00  --clausifier_options                    --mode clausify
% 2.11/1.00  --stdin                                 false
% 2.11/1.00  --stats_out                             all
% 2.11/1.00  
% 2.11/1.00  ------ General Options
% 2.11/1.00  
% 2.11/1.00  --fof                                   false
% 2.11/1.00  --time_out_real                         305.
% 2.11/1.00  --time_out_virtual                      -1.
% 2.11/1.00  --symbol_type_check                     false
% 2.11/1.00  --clausify_out                          false
% 2.11/1.00  --sig_cnt_out                           false
% 2.11/1.00  --trig_cnt_out                          false
% 2.11/1.00  --trig_cnt_out_tolerance                1.
% 2.11/1.00  --trig_cnt_out_sk_spl                   false
% 2.11/1.00  --abstr_cl_out                          false
% 2.11/1.00  
% 2.11/1.00  ------ Global Options
% 2.11/1.00  
% 2.11/1.00  --schedule                              default
% 2.11/1.00  --add_important_lit                     false
% 2.11/1.00  --prop_solver_per_cl                    1000
% 2.11/1.00  --min_unsat_core                        false
% 2.11/1.00  --soft_assumptions                      false
% 2.11/1.00  --soft_lemma_size                       3
% 2.11/1.00  --prop_impl_unit_size                   0
% 2.11/1.00  --prop_impl_unit                        []
% 2.11/1.00  --share_sel_clauses                     true
% 2.11/1.00  --reset_solvers                         false
% 2.11/1.00  --bc_imp_inh                            [conj_cone]
% 2.11/1.00  --conj_cone_tolerance                   3.
% 2.11/1.00  --extra_neg_conj                        none
% 2.11/1.00  --large_theory_mode                     true
% 2.11/1.00  --prolific_symb_bound                   200
% 2.11/1.00  --lt_threshold                          2000
% 2.11/1.00  --clause_weak_htbl                      true
% 2.11/1.00  --gc_record_bc_elim                     false
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing Options
% 2.11/1.00  
% 2.11/1.00  --preprocessing_flag                    true
% 2.11/1.00  --time_out_prep_mult                    0.1
% 2.11/1.00  --splitting_mode                        input
% 2.11/1.00  --splitting_grd                         true
% 2.11/1.00  --splitting_cvd                         false
% 2.11/1.00  --splitting_cvd_svl                     false
% 2.11/1.00  --splitting_nvd                         32
% 2.11/1.00  --sub_typing                            true
% 2.11/1.00  --prep_gs_sim                           true
% 2.11/1.00  --prep_unflatten                        true
% 2.11/1.00  --prep_res_sim                          true
% 2.11/1.00  --prep_upred                            true
% 2.11/1.00  --prep_sem_filter                       exhaustive
% 2.11/1.00  --prep_sem_filter_out                   false
% 2.11/1.00  --pred_elim                             true
% 2.11/1.00  --res_sim_input                         true
% 2.11/1.00  --eq_ax_congr_red                       true
% 2.11/1.00  --pure_diseq_elim                       true
% 2.11/1.00  --brand_transform                       false
% 2.11/1.00  --non_eq_to_eq                          false
% 2.11/1.00  --prep_def_merge                        true
% 2.11/1.00  --prep_def_merge_prop_impl              false
% 2.11/1.00  --prep_def_merge_mbd                    true
% 2.11/1.00  --prep_def_merge_tr_red                 false
% 2.11/1.00  --prep_def_merge_tr_cl                  false
% 2.11/1.00  --smt_preprocessing                     true
% 2.11/1.00  --smt_ac_axioms                         fast
% 2.11/1.00  --preprocessed_out                      false
% 2.11/1.00  --preprocessed_stats                    false
% 2.11/1.00  
% 2.11/1.00  ------ Abstraction refinement Options
% 2.11/1.00  
% 2.11/1.00  --abstr_ref                             []
% 2.11/1.00  --abstr_ref_prep                        false
% 2.11/1.00  --abstr_ref_until_sat                   false
% 2.11/1.00  --abstr_ref_sig_restrict                funpre
% 2.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.00  --abstr_ref_under                       []
% 2.11/1.00  
% 2.11/1.00  ------ SAT Options
% 2.11/1.00  
% 2.11/1.00  --sat_mode                              false
% 2.11/1.00  --sat_fm_restart_options                ""
% 2.11/1.00  --sat_gr_def                            false
% 2.11/1.00  --sat_epr_types                         true
% 2.11/1.00  --sat_non_cyclic_types                  false
% 2.11/1.00  --sat_finite_models                     false
% 2.11/1.00  --sat_fm_lemmas                         false
% 2.11/1.00  --sat_fm_prep                           false
% 2.11/1.00  --sat_fm_uc_incr                        true
% 2.11/1.00  --sat_out_model                         small
% 2.11/1.00  --sat_out_clauses                       false
% 2.11/1.00  
% 2.11/1.00  ------ QBF Options
% 2.11/1.00  
% 2.11/1.00  --qbf_mode                              false
% 2.11/1.00  --qbf_elim_univ                         false
% 2.11/1.00  --qbf_dom_inst                          none
% 2.11/1.00  --qbf_dom_pre_inst                      false
% 2.11/1.00  --qbf_sk_in                             false
% 2.11/1.00  --qbf_pred_elim                         true
% 2.11/1.00  --qbf_split                             512
% 2.11/1.00  
% 2.11/1.00  ------ BMC1 Options
% 2.11/1.00  
% 2.11/1.00  --bmc1_incremental                      false
% 2.11/1.00  --bmc1_axioms                           reachable_all
% 2.11/1.00  --bmc1_min_bound                        0
% 2.11/1.00  --bmc1_max_bound                        -1
% 2.11/1.00  --bmc1_max_bound_default                -1
% 2.11/1.00  --bmc1_symbol_reachability              true
% 2.11/1.00  --bmc1_property_lemmas                  false
% 2.11/1.00  --bmc1_k_induction                      false
% 2.11/1.00  --bmc1_non_equiv_states                 false
% 2.11/1.00  --bmc1_deadlock                         false
% 2.11/1.00  --bmc1_ucm                              false
% 2.11/1.00  --bmc1_add_unsat_core                   none
% 2.11/1.00  --bmc1_unsat_core_children              false
% 2.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.00  --bmc1_out_stat                         full
% 2.11/1.00  --bmc1_ground_init                      false
% 2.11/1.00  --bmc1_pre_inst_next_state              false
% 2.11/1.00  --bmc1_pre_inst_state                   false
% 2.11/1.00  --bmc1_pre_inst_reach_state             false
% 2.11/1.00  --bmc1_out_unsat_core                   false
% 2.11/1.00  --bmc1_aig_witness_out                  false
% 2.11/1.00  --bmc1_verbose                          false
% 2.11/1.00  --bmc1_dump_clauses_tptp                false
% 2.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.00  --bmc1_dump_file                        -
% 2.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.00  --bmc1_ucm_extend_mode                  1
% 2.11/1.00  --bmc1_ucm_init_mode                    2
% 2.11/1.00  --bmc1_ucm_cone_mode                    none
% 2.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.00  --bmc1_ucm_relax_model                  4
% 2.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.00  --bmc1_ucm_layered_model                none
% 2.11/1.00  --bmc1_ucm_max_lemma_size               10
% 2.11/1.00  
% 2.11/1.00  ------ AIG Options
% 2.11/1.00  
% 2.11/1.00  --aig_mode                              false
% 2.11/1.00  
% 2.11/1.00  ------ Instantiation Options
% 2.11/1.00  
% 2.11/1.00  --instantiation_flag                    true
% 2.11/1.00  --inst_sos_flag                         false
% 2.11/1.00  --inst_sos_phase                        true
% 2.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel_side                     num_symb
% 2.11/1.00  --inst_solver_per_active                1400
% 2.11/1.00  --inst_solver_calls_frac                1.
% 2.11/1.00  --inst_passive_queue_type               priority_queues
% 2.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.00  --inst_passive_queues_freq              [25;2]
% 2.11/1.00  --inst_dismatching                      true
% 2.11/1.00  --inst_eager_unprocessed_to_passive     true
% 2.11/1.00  --inst_prop_sim_given                   true
% 2.11/1.00  --inst_prop_sim_new                     false
% 2.11/1.00  --inst_subs_new                         false
% 2.11/1.00  --inst_eq_res_simp                      false
% 2.11/1.00  --inst_subs_given                       false
% 2.11/1.00  --inst_orphan_elimination               true
% 2.11/1.00  --inst_learning_loop_flag               true
% 2.11/1.00  --inst_learning_start                   3000
% 2.11/1.00  --inst_learning_factor                  2
% 2.11/1.00  --inst_start_prop_sim_after_learn       3
% 2.11/1.00  --inst_sel_renew                        solver
% 2.11/1.00  --inst_lit_activity_flag                true
% 2.11/1.00  --inst_restr_to_given                   false
% 2.11/1.00  --inst_activity_threshold               500
% 2.11/1.00  --inst_out_proof                        true
% 2.11/1.00  
% 2.11/1.00  ------ Resolution Options
% 2.11/1.00  
% 2.11/1.00  --resolution_flag                       true
% 2.11/1.00  --res_lit_sel                           adaptive
% 2.11/1.00  --res_lit_sel_side                      none
% 2.11/1.00  --res_ordering                          kbo
% 2.11/1.00  --res_to_prop_solver                    active
% 2.11/1.00  --res_prop_simpl_new                    false
% 2.11/1.00  --res_prop_simpl_given                  true
% 2.11/1.00  --res_passive_queue_type                priority_queues
% 2.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.00  --res_passive_queues_freq               [15;5]
% 2.11/1.00  --res_forward_subs                      full
% 2.11/1.00  --res_backward_subs                     full
% 2.11/1.00  --res_forward_subs_resolution           true
% 2.11/1.00  --res_backward_subs_resolution          true
% 2.11/1.00  --res_orphan_elimination                true
% 2.11/1.00  --res_time_limit                        2.
% 2.11/1.00  --res_out_proof                         true
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Options
% 2.11/1.00  
% 2.11/1.00  --superposition_flag                    true
% 2.11/1.00  --sup_passive_queue_type                priority_queues
% 2.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.00  --demod_completeness_check              fast
% 2.11/1.00  --demod_use_ground                      true
% 2.11/1.00  --sup_to_prop_solver                    passive
% 2.11/1.00  --sup_prop_simpl_new                    true
% 2.11/1.00  --sup_prop_simpl_given                  true
% 2.11/1.00  --sup_fun_splitting                     false
% 2.11/1.00  --sup_smt_interval                      50000
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Simplification Setup
% 2.11/1.00  
% 2.11/1.00  --sup_indices_passive                   []
% 2.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_full_bw                           [BwDemod]
% 2.11/1.00  --sup_immed_triv                        [TrivRules]
% 2.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_immed_bw_main                     []
% 2.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  
% 2.11/1.00  ------ Combination Options
% 2.11/1.00  
% 2.11/1.00  --comb_res_mult                         3
% 2.11/1.00  --comb_sup_mult                         2
% 2.11/1.00  --comb_inst_mult                        10
% 2.11/1.00  
% 2.11/1.00  ------ Debug Options
% 2.11/1.00  
% 2.11/1.00  --dbg_backtrace                         false
% 2.11/1.00  --dbg_dump_prop_clauses                 false
% 2.11/1.00  --dbg_dump_prop_clauses_file            -
% 2.11/1.00  --dbg_out_stat                          false
% 2.11/1.00  ------ Parsing...
% 2.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.11/1.00  ------ Proving...
% 2.11/1.00  ------ Problem Properties 
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  clauses                                 21
% 2.11/1.00  conjectures                             6
% 2.11/1.00  EPR                                     6
% 2.11/1.00  Horn                                    19
% 2.11/1.00  unary                                   2
% 2.11/1.00  binary                                  10
% 2.11/1.00  lits                                    54
% 2.11/1.00  lits eq                                 5
% 2.11/1.00  fd_pure                                 0
% 2.11/1.00  fd_pseudo                               0
% 2.11/1.00  fd_cond                                 2
% 2.11/1.00  fd_pseudo_cond                          0
% 2.11/1.00  AC symbols                              0
% 2.11/1.00  
% 2.11/1.00  ------ Schedule dynamic 5 is on 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  ------ 
% 2.11/1.00  Current options:
% 2.11/1.00  ------ 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options
% 2.11/1.00  
% 2.11/1.00  --out_options                           all
% 2.11/1.00  --tptp_safe_out                         true
% 2.11/1.00  --problem_path                          ""
% 2.11/1.00  --include_path                          ""
% 2.11/1.00  --clausifier                            res/vclausify_rel
% 2.11/1.00  --clausifier_options                    --mode clausify
% 2.11/1.00  --stdin                                 false
% 2.11/1.00  --stats_out                             all
% 2.11/1.00  
% 2.11/1.00  ------ General Options
% 2.11/1.00  
% 2.11/1.00  --fof                                   false
% 2.11/1.00  --time_out_real                         305.
% 2.11/1.00  --time_out_virtual                      -1.
% 2.11/1.00  --symbol_type_check                     false
% 2.11/1.00  --clausify_out                          false
% 2.11/1.00  --sig_cnt_out                           false
% 2.11/1.00  --trig_cnt_out                          false
% 2.11/1.00  --trig_cnt_out_tolerance                1.
% 2.11/1.00  --trig_cnt_out_sk_spl                   false
% 2.11/1.00  --abstr_cl_out                          false
% 2.11/1.00  
% 2.11/1.00  ------ Global Options
% 2.11/1.00  
% 2.11/1.00  --schedule                              default
% 2.11/1.00  --add_important_lit                     false
% 2.11/1.00  --prop_solver_per_cl                    1000
% 2.11/1.00  --min_unsat_core                        false
% 2.11/1.00  --soft_assumptions                      false
% 2.11/1.00  --soft_lemma_size                       3
% 2.11/1.00  --prop_impl_unit_size                   0
% 2.11/1.00  --prop_impl_unit                        []
% 2.11/1.00  --share_sel_clauses                     true
% 2.11/1.00  --reset_solvers                         false
% 2.11/1.00  --bc_imp_inh                            [conj_cone]
% 2.11/1.00  --conj_cone_tolerance                   3.
% 2.11/1.00  --extra_neg_conj                        none
% 2.11/1.00  --large_theory_mode                     true
% 2.11/1.00  --prolific_symb_bound                   200
% 2.11/1.00  --lt_threshold                          2000
% 2.11/1.00  --clause_weak_htbl                      true
% 2.11/1.00  --gc_record_bc_elim                     false
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing Options
% 2.11/1.00  
% 2.11/1.00  --preprocessing_flag                    true
% 2.11/1.00  --time_out_prep_mult                    0.1
% 2.11/1.00  --splitting_mode                        input
% 2.11/1.00  --splitting_grd                         true
% 2.11/1.00  --splitting_cvd                         false
% 2.11/1.00  --splitting_cvd_svl                     false
% 2.11/1.00  --splitting_nvd                         32
% 2.11/1.00  --sub_typing                            true
% 2.11/1.00  --prep_gs_sim                           true
% 2.11/1.00  --prep_unflatten                        true
% 2.11/1.00  --prep_res_sim                          true
% 2.11/1.00  --prep_upred                            true
% 2.11/1.00  --prep_sem_filter                       exhaustive
% 2.11/1.00  --prep_sem_filter_out                   false
% 2.11/1.00  --pred_elim                             true
% 2.11/1.00  --res_sim_input                         true
% 2.11/1.01  --eq_ax_congr_red                       true
% 2.11/1.01  --pure_diseq_elim                       true
% 2.11/1.01  --brand_transform                       false
% 2.11/1.01  --non_eq_to_eq                          false
% 2.11/1.01  --prep_def_merge                        true
% 2.11/1.01  --prep_def_merge_prop_impl              false
% 2.11/1.01  --prep_def_merge_mbd                    true
% 2.11/1.01  --prep_def_merge_tr_red                 false
% 2.11/1.01  --prep_def_merge_tr_cl                  false
% 2.11/1.01  --smt_preprocessing                     true
% 2.11/1.01  --smt_ac_axioms                         fast
% 2.11/1.01  --preprocessed_out                      false
% 2.11/1.01  --preprocessed_stats                    false
% 2.11/1.01  
% 2.11/1.01  ------ Abstraction refinement Options
% 2.11/1.01  
% 2.11/1.01  --abstr_ref                             []
% 2.11/1.01  --abstr_ref_prep                        false
% 2.11/1.01  --abstr_ref_until_sat                   false
% 2.11/1.01  --abstr_ref_sig_restrict                funpre
% 2.11/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.01  --abstr_ref_under                       []
% 2.11/1.01  
% 2.11/1.01  ------ SAT Options
% 2.11/1.01  
% 2.11/1.01  --sat_mode                              false
% 2.11/1.01  --sat_fm_restart_options                ""
% 2.11/1.01  --sat_gr_def                            false
% 2.11/1.01  --sat_epr_types                         true
% 2.11/1.01  --sat_non_cyclic_types                  false
% 2.11/1.01  --sat_finite_models                     false
% 2.11/1.01  --sat_fm_lemmas                         false
% 2.11/1.01  --sat_fm_prep                           false
% 2.11/1.01  --sat_fm_uc_incr                        true
% 2.11/1.01  --sat_out_model                         small
% 2.11/1.01  --sat_out_clauses                       false
% 2.11/1.01  
% 2.11/1.01  ------ QBF Options
% 2.11/1.01  
% 2.11/1.01  --qbf_mode                              false
% 2.11/1.01  --qbf_elim_univ                         false
% 2.11/1.01  --qbf_dom_inst                          none
% 2.11/1.01  --qbf_dom_pre_inst                      false
% 2.11/1.01  --qbf_sk_in                             false
% 2.11/1.01  --qbf_pred_elim                         true
% 2.11/1.01  --qbf_split                             512
% 2.11/1.01  
% 2.11/1.01  ------ BMC1 Options
% 2.11/1.01  
% 2.11/1.01  --bmc1_incremental                      false
% 2.11/1.01  --bmc1_axioms                           reachable_all
% 2.11/1.01  --bmc1_min_bound                        0
% 2.11/1.01  --bmc1_max_bound                        -1
% 2.11/1.01  --bmc1_max_bound_default                -1
% 2.11/1.01  --bmc1_symbol_reachability              true
% 2.11/1.01  --bmc1_property_lemmas                  false
% 2.11/1.01  --bmc1_k_induction                      false
% 2.11/1.01  --bmc1_non_equiv_states                 false
% 2.11/1.01  --bmc1_deadlock                         false
% 2.11/1.01  --bmc1_ucm                              false
% 2.11/1.01  --bmc1_add_unsat_core                   none
% 2.11/1.01  --bmc1_unsat_core_children              false
% 2.11/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.01  --bmc1_out_stat                         full
% 2.11/1.01  --bmc1_ground_init                      false
% 2.11/1.01  --bmc1_pre_inst_next_state              false
% 2.11/1.01  --bmc1_pre_inst_state                   false
% 2.11/1.01  --bmc1_pre_inst_reach_state             false
% 2.11/1.01  --bmc1_out_unsat_core                   false
% 2.11/1.01  --bmc1_aig_witness_out                  false
% 2.11/1.01  --bmc1_verbose                          false
% 2.11/1.01  --bmc1_dump_clauses_tptp                false
% 2.11/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.01  --bmc1_dump_file                        -
% 2.11/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.01  --bmc1_ucm_extend_mode                  1
% 2.11/1.01  --bmc1_ucm_init_mode                    2
% 2.11/1.01  --bmc1_ucm_cone_mode                    none
% 2.11/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.01  --bmc1_ucm_relax_model                  4
% 2.11/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.01  --bmc1_ucm_layered_model                none
% 2.11/1.01  --bmc1_ucm_max_lemma_size               10
% 2.11/1.01  
% 2.11/1.01  ------ AIG Options
% 2.11/1.01  
% 2.11/1.01  --aig_mode                              false
% 2.11/1.01  
% 2.11/1.01  ------ Instantiation Options
% 2.11/1.01  
% 2.11/1.01  --instantiation_flag                    true
% 2.11/1.01  --inst_sos_flag                         false
% 2.11/1.01  --inst_sos_phase                        true
% 2.11/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.01  --inst_lit_sel_side                     none
% 2.11/1.01  --inst_solver_per_active                1400
% 2.11/1.01  --inst_solver_calls_frac                1.
% 2.11/1.01  --inst_passive_queue_type               priority_queues
% 2.11/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.01  --inst_passive_queues_freq              [25;2]
% 2.11/1.01  --inst_dismatching                      true
% 2.11/1.01  --inst_eager_unprocessed_to_passive     true
% 2.11/1.01  --inst_prop_sim_given                   true
% 2.11/1.01  --inst_prop_sim_new                     false
% 2.11/1.01  --inst_subs_new                         false
% 2.11/1.01  --inst_eq_res_simp                      false
% 2.11/1.01  --inst_subs_given                       false
% 2.11/1.01  --inst_orphan_elimination               true
% 2.11/1.01  --inst_learning_loop_flag               true
% 2.11/1.01  --inst_learning_start                   3000
% 2.11/1.01  --inst_learning_factor                  2
% 2.11/1.01  --inst_start_prop_sim_after_learn       3
% 2.11/1.01  --inst_sel_renew                        solver
% 2.11/1.01  --inst_lit_activity_flag                true
% 2.11/1.01  --inst_restr_to_given                   false
% 2.11/1.01  --inst_activity_threshold               500
% 2.11/1.01  --inst_out_proof                        true
% 2.11/1.01  
% 2.11/1.01  ------ Resolution Options
% 2.11/1.01  
% 2.11/1.01  --resolution_flag                       false
% 2.11/1.01  --res_lit_sel                           adaptive
% 2.11/1.01  --res_lit_sel_side                      none
% 2.11/1.01  --res_ordering                          kbo
% 2.11/1.01  --res_to_prop_solver                    active
% 2.11/1.01  --res_prop_simpl_new                    false
% 2.11/1.01  --res_prop_simpl_given                  true
% 2.11/1.01  --res_passive_queue_type                priority_queues
% 2.11/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.01  --res_passive_queues_freq               [15;5]
% 2.11/1.01  --res_forward_subs                      full
% 2.11/1.01  --res_backward_subs                     full
% 2.11/1.01  --res_forward_subs_resolution           true
% 2.11/1.01  --res_backward_subs_resolution          true
% 2.11/1.01  --res_orphan_elimination                true
% 2.11/1.01  --res_time_limit                        2.
% 2.11/1.01  --res_out_proof                         true
% 2.11/1.01  
% 2.11/1.01  ------ Superposition Options
% 2.11/1.01  
% 2.11/1.01  --superposition_flag                    true
% 2.11/1.01  --sup_passive_queue_type                priority_queues
% 2.11/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.01  --demod_completeness_check              fast
% 2.11/1.01  --demod_use_ground                      true
% 2.11/1.01  --sup_to_prop_solver                    passive
% 2.11/1.01  --sup_prop_simpl_new                    true
% 2.11/1.01  --sup_prop_simpl_given                  true
% 2.11/1.01  --sup_fun_splitting                     false
% 2.11/1.01  --sup_smt_interval                      50000
% 2.11/1.01  
% 2.11/1.01  ------ Superposition Simplification Setup
% 2.11/1.01  
% 2.11/1.01  --sup_indices_passive                   []
% 2.11/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.01  --sup_full_bw                           [BwDemod]
% 2.11/1.01  --sup_immed_triv                        [TrivRules]
% 2.11/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.01  --sup_immed_bw_main                     []
% 2.11/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.01  
% 2.11/1.01  ------ Combination Options
% 2.11/1.01  
% 2.11/1.01  --comb_res_mult                         3
% 2.11/1.01  --comb_sup_mult                         2
% 2.11/1.01  --comb_inst_mult                        10
% 2.11/1.01  
% 2.11/1.01  ------ Debug Options
% 2.11/1.01  
% 2.11/1.01  --dbg_backtrace                         false
% 2.11/1.01  --dbg_dump_prop_clauses                 false
% 2.11/1.01  --dbg_dump_prop_clauses_file            -
% 2.11/1.01  --dbg_out_stat                          false
% 2.11/1.01  
% 2.11/1.01  
% 2.11/1.01  
% 2.11/1.01  
% 2.11/1.01  ------ Proving...
% 2.11/1.01  
% 2.11/1.01  
% 2.11/1.01  % SZS status Theorem for theBenchmark.p
% 2.11/1.01  
% 2.11/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/1.01  
% 2.11/1.01  fof(f1,axiom,(
% 2.11/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f13,plain,(
% 2.11/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.11/1.01    inference(ennf_transformation,[],[f1])).
% 2.11/1.01  
% 2.11/1.01  fof(f25,plain,(
% 2.11/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.11/1.01    introduced(choice_axiom,[])).
% 2.11/1.01  
% 2.11/1.01  fof(f26,plain,(
% 2.11/1.01    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.11/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).
% 2.11/1.01  
% 2.11/1.01  fof(f40,plain,(
% 2.11/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.11/1.01    inference(cnf_transformation,[],[f26])).
% 2.11/1.01  
% 2.11/1.01  fof(f11,conjecture,(
% 2.11/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f12,negated_conjecture,(
% 2.11/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.11/1.01    inference(negated_conjecture,[],[f11])).
% 2.11/1.01  
% 2.11/1.01  fof(f23,plain,(
% 2.11/1.01    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.11/1.01    inference(ennf_transformation,[],[f12])).
% 2.11/1.01  
% 2.11/1.01  fof(f24,plain,(
% 2.11/1.01    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.11/1.01    inference(flattening,[],[f23])).
% 2.11/1.01  
% 2.11/1.01  fof(f33,plain,(
% 2.11/1.01    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.11/1.01    inference(nnf_transformation,[],[f24])).
% 2.11/1.01  
% 2.11/1.01  fof(f34,plain,(
% 2.11/1.01    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.11/1.01    inference(flattening,[],[f33])).
% 2.11/1.01  
% 2.11/1.01  fof(f35,plain,(
% 2.11/1.01    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.11/1.01    inference(rectify,[],[f34])).
% 2.11/1.01  
% 2.11/1.01  fof(f38,plain,(
% 2.11/1.01    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK4 & v3_pre_topc(sK4,X0) & r1_tarski(sK4,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.11/1.01    introduced(choice_axiom,[])).
% 2.11/1.01  
% 2.11/1.01  fof(f37,plain,(
% 2.11/1.01    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK3,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.11/1.01    introduced(choice_axiom,[])).
% 2.11/1.01  
% 2.11/1.01  fof(f36,plain,(
% 2.11/1.01    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(X1,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 2.11/1.01    introduced(choice_axiom,[])).
% 2.11/1.01  
% 2.11/1.01  fof(f39,plain,(
% 2.11/1.01    (((k1_xboole_0 != sK4 & v3_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(sK3,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 2.11/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).
% 2.11/1.01  
% 2.11/1.01  fof(f59,plain,(
% 2.11/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tops_1(sK3,sK2)),
% 2.11/1.01    inference(cnf_transformation,[],[f39])).
% 2.11/1.01  
% 2.11/1.01  fof(f9,axiom,(
% 2.11/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f20,plain,(
% 2.11/1.01    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.11/1.01    inference(ennf_transformation,[],[f9])).
% 2.11/1.01  
% 2.11/1.01  fof(f21,plain,(
% 2.11/1.01    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.11/1.01    inference(flattening,[],[f20])).
% 2.11/1.01  
% 2.11/1.01  fof(f28,plain,(
% 2.11/1.01    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.11/1.01    inference(nnf_transformation,[],[f21])).
% 2.11/1.01  
% 2.11/1.01  fof(f29,plain,(
% 2.11/1.01    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.11/1.01    inference(rectify,[],[f28])).
% 2.11/1.01  
% 2.11/1.01  fof(f30,plain,(
% 2.11/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.11/1.01    introduced(choice_axiom,[])).
% 2.11/1.01  
% 2.11/1.01  fof(f31,plain,(
% 2.11/1.01    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.11/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 2.11/1.01  
% 2.11/1.01  fof(f52,plain,(
% 2.11/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f31])).
% 2.11/1.01  
% 2.11/1.01  fof(f55,plain,(
% 2.11/1.01    v2_pre_topc(sK2)),
% 2.11/1.01    inference(cnf_transformation,[],[f39])).
% 2.11/1.01  
% 2.11/1.01  fof(f56,plain,(
% 2.11/1.01    l1_pre_topc(sK2)),
% 2.11/1.01    inference(cnf_transformation,[],[f39])).
% 2.11/1.01  
% 2.11/1.01  fof(f10,axiom,(
% 2.11/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f22,plain,(
% 2.11/1.01    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/1.01    inference(ennf_transformation,[],[f10])).
% 2.11/1.01  
% 2.11/1.01  fof(f32,plain,(
% 2.11/1.01    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/1.01    inference(nnf_transformation,[],[f22])).
% 2.11/1.01  
% 2.11/1.01  fof(f54,plain,(
% 2.11/1.01    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f32])).
% 2.11/1.01  
% 2.11/1.01  fof(f57,plain,(
% 2.11/1.01    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.11/1.01    inference(cnf_transformation,[],[f39])).
% 2.11/1.01  
% 2.11/1.01  fof(f61,plain,(
% 2.11/1.01    v3_pre_topc(sK4,sK2) | ~v2_tops_1(sK3,sK2)),
% 2.11/1.01    inference(cnf_transformation,[],[f39])).
% 2.11/1.01  
% 2.11/1.01  fof(f53,plain,(
% 2.11/1.01    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f32])).
% 2.11/1.01  
% 2.11/1.01  fof(f7,axiom,(
% 2.11/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f17,plain,(
% 2.11/1.01    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.11/1.01    inference(ennf_transformation,[],[f7])).
% 2.11/1.01  
% 2.11/1.01  fof(f18,plain,(
% 2.11/1.01    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.11/1.01    inference(flattening,[],[f17])).
% 2.11/1.01  
% 2.11/1.01  fof(f46,plain,(
% 2.11/1.01    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f18])).
% 2.11/1.01  
% 2.11/1.01  fof(f8,axiom,(
% 2.11/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f19,plain,(
% 2.11/1.01    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/1.01    inference(ennf_transformation,[],[f8])).
% 2.11/1.01  
% 2.11/1.01  fof(f47,plain,(
% 2.11/1.01    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f19])).
% 2.11/1.01  
% 2.11/1.01  fof(f5,axiom,(
% 2.11/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f27,plain,(
% 2.11/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.11/1.01    inference(nnf_transformation,[],[f5])).
% 2.11/1.01  
% 2.11/1.01  fof(f43,plain,(
% 2.11/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.11/1.01    inference(cnf_transformation,[],[f27])).
% 2.11/1.01  
% 2.11/1.01  fof(f2,axiom,(
% 2.11/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f14,plain,(
% 2.11/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.11/1.01    inference(ennf_transformation,[],[f2])).
% 2.11/1.01  
% 2.11/1.01  fof(f15,plain,(
% 2.11/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.11/1.01    inference(flattening,[],[f14])).
% 2.11/1.01  
% 2.11/1.01  fof(f41,plain,(
% 2.11/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f15])).
% 2.11/1.01  
% 2.11/1.01  fof(f58,plain,(
% 2.11/1.01    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f39])).
% 2.11/1.01  
% 2.11/1.01  fof(f44,plain,(
% 2.11/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f27])).
% 2.11/1.01  
% 2.11/1.01  fof(f3,axiom,(
% 2.11/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f42,plain,(
% 2.11/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f3])).
% 2.11/1.01  
% 2.11/1.01  fof(f60,plain,(
% 2.11/1.01    r1_tarski(sK4,sK3) | ~v2_tops_1(sK3,sK2)),
% 2.11/1.01    inference(cnf_transformation,[],[f39])).
% 2.11/1.01  
% 2.11/1.01  fof(f6,axiom,(
% 2.11/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.01  
% 2.11/1.01  fof(f16,plain,(
% 2.11/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.11/1.01    inference(ennf_transformation,[],[f6])).
% 2.11/1.01  
% 2.11/1.01  fof(f45,plain,(
% 2.11/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.11/1.01    inference(cnf_transformation,[],[f16])).
% 2.11/1.01  
% 2.11/1.01  fof(f62,plain,(
% 2.11/1.01    k1_xboole_0 != sK4 | ~v2_tops_1(sK3,sK2)),
% 2.11/1.01    inference(cnf_transformation,[],[f39])).
% 2.11/1.01  
% 2.11/1.01  cnf(c_0,plain,
% 2.11/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.11/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1917,plain,
% 2.11/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_18,negated_conjecture,
% 2.11/1.01      ( ~ v2_tops_1(sK3,sK2)
% 2.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.11/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1908,plain,
% 2.11/1.01      ( v2_tops_1(sK3,sK2) != iProver_top
% 2.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_8,plain,
% 2.11/1.01      ( ~ v3_pre_topc(X0,X1)
% 2.11/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | ~ r1_tarski(X0,X2)
% 2.11/1.01      | ~ r2_hidden(X3,X0)
% 2.11/1.01      | r2_hidden(X3,k1_tops_1(X1,X2))
% 2.11/1.01      | ~ v2_pre_topc(X1)
% 2.11/1.01      | ~ l1_pre_topc(X1) ),
% 2.11/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_22,negated_conjecture,
% 2.11/1.01      ( v2_pre_topc(sK2) ),
% 2.11/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_411,plain,
% 2.11/1.01      ( ~ v3_pre_topc(X0,X1)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | ~ r1_tarski(X0,X2)
% 2.11/1.01      | ~ r2_hidden(X3,X0)
% 2.11/1.01      | r2_hidden(X3,k1_tops_1(X1,X2))
% 2.11/1.01      | ~ l1_pre_topc(X1)
% 2.11/1.01      | sK2 != X1 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_412,plain,
% 2.11/1.01      ( ~ v3_pre_topc(X0,sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ r1_tarski(X0,X1)
% 2.11/1.01      | ~ r2_hidden(X2,X0)
% 2.11/1.01      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 2.11/1.01      | ~ l1_pre_topc(sK2) ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_411]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_21,negated_conjecture,
% 2.11/1.01      ( l1_pre_topc(sK2) ),
% 2.11/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_414,plain,
% 2.11/1.01      ( r2_hidden(X2,k1_tops_1(sK2,X1))
% 2.11/1.01      | ~ r2_hidden(X2,X0)
% 2.11/1.01      | ~ r1_tarski(X0,X1)
% 2.11/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ v3_pre_topc(X0,sK2) ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_412,c_21]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_415,plain,
% 2.11/1.01      ( ~ v3_pre_topc(X0,sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ r1_tarski(X0,X1)
% 2.11/1.01      | ~ r2_hidden(X2,X0)
% 2.11/1.01      | r2_hidden(X2,k1_tops_1(sK2,X1)) ),
% 2.11/1.01      inference(renaming,[status(thm)],[c_414]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1900,plain,
% 2.11/1.01      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.11/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.11/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.11/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.11/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.11/1.01      | r2_hidden(X2,k1_tops_1(sK2,X1)) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2873,plain,
% 2.11/1.01      ( v2_tops_1(sK3,sK2) != iProver_top
% 2.11/1.01      | v3_pre_topc(sK4,sK2) != iProver_top
% 2.11/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.11/1.01      | r1_tarski(sK4,X0) != iProver_top
% 2.11/1.01      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 2.11/1.01      | r2_hidden(X1,sK4) != iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_1908,c_1900]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_13,plain,
% 2.11/1.01      ( v2_tops_1(X0,X1)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | ~ l1_pre_topc(X1)
% 2.11/1.01      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.11/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_478,plain,
% 2.11/1.01      ( v2_tops_1(X0,X1)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.11/1.01      | sK2 != X1 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_479,plain,
% 2.11/1.01      ( v2_tops_1(X0,sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,X0) != k1_xboole_0 ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_478]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_775,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,X0) != k1_xboole_0
% 2.11/1.01      | sK2 != sK2
% 2.11/1.01      | sK3 != X0 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_479]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_776,plain,
% 2.11/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_775]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_20,negated_conjecture,
% 2.11/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.11/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_778,plain,
% 2.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_776,c_20]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_780,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 2.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_16,negated_conjecture,
% 2.11/1.01      ( ~ v2_tops_1(sK3,sK2) | v3_pre_topc(sK4,sK2) ),
% 2.11/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_803,plain,
% 2.11/1.01      ( v3_pre_topc(sK4,sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,X0) != k1_xboole_0
% 2.11/1.01      | sK2 != sK2
% 2.11/1.01      | sK3 != X0 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_479]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_804,plain,
% 2.11/1.01      ( v3_pre_topc(sK4,sK2)
% 2.11/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_803]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_806,plain,
% 2.11/1.01      ( v3_pre_topc(sK4,sK2) | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_804,c_20]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_808,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 2.11/1.01      | v3_pre_topc(sK4,sK2) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2716,plain,
% 2.11/1.01      ( ~ v3_pre_topc(sK4,sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ r1_tarski(sK4,X0)
% 2.11/1.01      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 2.11/1.01      | ~ r2_hidden(X1,sK4) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_415]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2717,plain,
% 2.11/1.01      ( v3_pre_topc(sK4,sK2) != iProver_top
% 2.11/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.11/1.01      | r1_tarski(sK4,X0) != iProver_top
% 2.11/1.01      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 2.11/1.01      | r2_hidden(X1,sK4) != iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2716]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1906,plain,
% 2.11/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_14,plain,
% 2.11/1.01      ( ~ v2_tops_1(X0,X1)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | ~ l1_pre_topc(X1)
% 2.11/1.01      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.11/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_463,plain,
% 2.11/1.01      ( ~ v2_tops_1(X0,X1)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.11/1.01      | sK2 != X1 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_464,plain,
% 2.11/1.01      ( ~ v2_tops_1(X0,sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,X0) = k1_xboole_0 ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_463]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1899,plain,
% 2.11/1.01      ( k1_tops_1(sK2,X0) = k1_xboole_0
% 2.11/1.01      | v2_tops_1(X0,sK2) != iProver_top
% 2.11/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2801,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 2.11/1.01      | v2_tops_1(sK3,sK2) != iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_1906,c_1899]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_6,plain,
% 2.11/1.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.11/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.11/1.01      | ~ v2_pre_topc(X0)
% 2.11/1.01      | ~ l1_pre_topc(X0) ),
% 2.11/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_330,plain,
% 2.11/1.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.11/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.11/1.01      | ~ l1_pre_topc(X0)
% 2.11/1.01      | sK2 != X0 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_331,plain,
% 2.11/1.01      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ l1_pre_topc(sK2) ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_330]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_335,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_331,c_21]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_336,plain,
% 2.11/1.01      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.11/1.01      inference(renaming,[status(thm)],[c_335]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2073,plain,
% 2.11/1.01      ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
% 2.11/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_336]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_7,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.11/1.01      | ~ l1_pre_topc(X1) ),
% 2.11/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_493,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/1.01      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.11/1.01      | sK2 != X1 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_494,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_493]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2079,plain,
% 2.11/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_494]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_4,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.11/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2112,plain,
% 2.11/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | r1_tarski(sK3,u1_struct_0(sK2)) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1376,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2171,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) != X0
% 2.11/1.01      | k1_tops_1(sK2,sK3) = k1_xboole_0
% 2.11/1.01      | k1_xboole_0 != X0 ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_1376]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2320,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) != k1_tops_1(sK2,sK3)
% 2.11/1.01      | k1_tops_1(sK2,sK3) = k1_xboole_0
% 2.11/1.01      | k1_xboole_0 != k1_tops_1(sK2,sK3) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_2171]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1375,plain,( X0 = X0 ),theory(equality) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2321,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) = k1_tops_1(sK2,sK3) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_1375]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1,plain,
% 2.11/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.11/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2190,plain,
% 2.11/1.01      ( r1_tarski(X0,u1_struct_0(sK2))
% 2.11/1.01      | ~ r1_tarski(X0,sK3)
% 2.11/1.01      | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2337,plain,
% 2.11/1.01      ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2))
% 2.11/1.01      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 2.11/1.01      | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_2190]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_19,negated_conjecture,
% 2.11/1.01      ( v2_tops_1(sK3,sK2)
% 2.11/1.01      | ~ v3_pre_topc(X0,sK2)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ r1_tarski(X0,sK3)
% 2.11/1.01      | k1_xboole_0 = X0 ),
% 2.11/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2382,plain,
% 2.11/1.01      ( v2_tops_1(sK3,sK2)
% 2.11/1.01      | ~ v3_pre_topc(k1_tops_1(sK2,sK3),sK2)
% 2.11/1.01      | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 2.11/1.01      | k1_xboole_0 = k1_tops_1(sK2,sK3) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3,plain,
% 2.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.11/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2589,plain,
% 2.11/1.01      ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | ~ r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2813,plain,
% 2.11/1.01      ( ~ v2_tops_1(sK3,sK2) | k1_tops_1(sK2,sK3) = k1_xboole_0 ),
% 2.11/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2801]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2855,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_2801,c_20,c_2073,c_2079,c_2112,c_2320,c_2321,c_2337,
% 2.11/1.01                 c_2382,c_2589,c_2813]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3610,plain,
% 2.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.11/1.01      | r1_tarski(sK4,X0) != iProver_top
% 2.11/1.01      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 2.11/1.01      | r2_hidden(X1,sK4) != iProver_top ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_2873,c_20,c_780,c_808,c_2073,c_2079,c_2112,c_2320,
% 2.11/1.01                 c_2321,c_2337,c_2382,c_2589,c_2717,c_2813]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3621,plain,
% 2.11/1.01      ( v2_tops_1(sK3,sK2) != iProver_top
% 2.11/1.01      | r1_tarski(sK4,sK4) != iProver_top
% 2.11/1.01      | r2_hidden(X0,k1_tops_1(sK2,sK4)) = iProver_top
% 2.11/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_1908,c_3610]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2,plain,
% 2.11/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.11/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_69,plain,
% 2.11/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_17,negated_conjecture,
% 2.11/1.01      ( ~ v2_tops_1(sK3,sK2) | r1_tarski(sK4,sK3) ),
% 2.11/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_789,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | r1_tarski(sK4,sK3)
% 2.11/1.01      | k1_tops_1(sK2,X0) != k1_xboole_0
% 2.11/1.01      | sK2 != sK2
% 2.11/1.01      | sK3 != X0 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_479]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_790,plain,
% 2.11/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | r1_tarski(sK4,sK3)
% 2.11/1.01      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_789]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_792,plain,
% 2.11/1.01      ( r1_tarski(sK4,sK3) | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_790,c_20]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_794,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 2.11/1.01      | r1_tarski(sK4,sK3) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_5,plain,
% 2.11/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.11/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2121,plain,
% 2.11/1.01      ( ~ r1_tarski(k1_xboole_0,X0) | ~ r2_hidden(X0,k1_xboole_0) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2122,plain,
% 2.11/1.01      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.11/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2121]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3622,plain,
% 2.11/1.01      ( r1_tarski(sK4,sK3) != iProver_top
% 2.11/1.01      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 2.11/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_1906,c_3610]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3637,plain,
% 2.11/1.01      ( r1_tarski(sK4,sK3) != iProver_top
% 2.11/1.01      | r2_hidden(X0,sK4) != iProver_top
% 2.11/1.01      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.11/1.01      inference(light_normalisation,[status(thm)],[c_3622,c_2855]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3901,plain,
% 2.11/1.01      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_3621,c_20,c_69,c_794,c_2073,c_2079,c_2112,c_2122,
% 2.11/1.01                 c_2320,c_2321,c_2337,c_2382,c_2589,c_2813,c_3637]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3908,plain,
% 2.11/1.01      ( sK4 = k1_xboole_0 ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_1917,c_3901]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_15,negated_conjecture,
% 2.11/1.01      ( ~ v2_tops_1(sK3,sK2) | k1_xboole_0 != sK4 ),
% 2.11/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_817,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,X0) != k1_xboole_0
% 2.11/1.01      | sK2 != sK2
% 2.11/1.01      | sK3 != X0
% 2.11/1.01      | sK4 != k1_xboole_0 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_479]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_818,plain,
% 2.11/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.11/1.01      | k1_tops_1(sK2,sK3) != k1_xboole_0
% 2.11/1.01      | sK4 != k1_xboole_0 ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_817]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_820,plain,
% 2.11/1.01      ( k1_tops_1(sK2,sK3) != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_818,c_20]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(contradiction,plain,
% 2.11/1.01      ( $false ),
% 2.11/1.01      inference(minisat,[status(thm)],[c_3908,c_2855,c_820]) ).
% 2.11/1.01  
% 2.11/1.01  
% 2.11/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/1.01  
% 2.11/1.01  ------                               Statistics
% 2.11/1.01  
% 2.11/1.01  ------ General
% 2.11/1.01  
% 2.11/1.01  abstr_ref_over_cycles:                  0
% 2.11/1.01  abstr_ref_under_cycles:                 0
% 2.11/1.01  gc_basic_clause_elim:                   0
% 2.11/1.01  forced_gc_time:                         0
% 2.11/1.01  parsing_time:                           0.014
% 2.11/1.01  unif_index_cands_time:                  0.
% 2.11/1.01  unif_index_add_time:                    0.
% 2.11/1.01  orderings_time:                         0.
% 2.11/1.01  out_proof_time:                         0.011
% 2.11/1.01  total_time:                             0.137
% 2.11/1.01  num_of_symbols:                         47
% 2.11/1.01  num_of_terms:                           2058
% 2.11/1.01  
% 2.11/1.01  ------ Preprocessing
% 2.11/1.01  
% 2.11/1.01  num_of_splits:                          0
% 2.11/1.01  num_of_split_atoms:                     0
% 2.11/1.01  num_of_reused_defs:                     0
% 2.11/1.01  num_eq_ax_congr_red:                    14
% 2.11/1.01  num_of_sem_filtered_clauses:            1
% 2.11/1.01  num_of_subtypes:                        0
% 2.11/1.01  monotx_restored_types:                  0
% 2.11/1.01  sat_num_of_epr_types:                   0
% 2.11/1.01  sat_num_of_non_cyclic_types:            0
% 2.11/1.01  sat_guarded_non_collapsed_types:        0
% 2.11/1.01  num_pure_diseq_elim:                    0
% 2.11/1.01  simp_replaced_by:                       0
% 2.11/1.01  res_preprocessed:                       109
% 2.11/1.01  prep_upred:                             0
% 2.11/1.01  prep_unflattend:                        31
% 2.11/1.01  smt_new_axioms:                         0
% 2.11/1.01  pred_elim_cands:                        5
% 2.11/1.01  pred_elim:                              2
% 2.11/1.01  pred_elim_cl:                           2
% 2.11/1.01  pred_elim_cycles:                       6
% 2.11/1.01  merged_defs:                            8
% 2.11/1.01  merged_defs_ncl:                        0
% 2.11/1.01  bin_hyper_res:                          8
% 2.11/1.01  prep_cycles:                            4
% 2.11/1.01  pred_elim_time:                         0.016
% 2.11/1.01  splitting_time:                         0.
% 2.11/1.01  sem_filter_time:                        0.
% 2.11/1.01  monotx_time:                            0.001
% 2.11/1.01  subtype_inf_time:                       0.
% 2.11/1.01  
% 2.11/1.01  ------ Problem properties
% 2.11/1.01  
% 2.11/1.01  clauses:                                21
% 2.11/1.01  conjectures:                            6
% 2.11/1.01  epr:                                    6
% 2.11/1.01  horn:                                   19
% 2.11/1.01  ground:                                 5
% 2.11/1.01  unary:                                  2
% 2.11/1.01  binary:                                 10
% 2.11/1.01  lits:                                   54
% 2.11/1.01  lits_eq:                                5
% 2.11/1.01  fd_pure:                                0
% 2.11/1.01  fd_pseudo:                              0
% 2.11/1.01  fd_cond:                                2
% 2.11/1.01  fd_pseudo_cond:                         0
% 2.11/1.01  ac_symbols:                             0
% 2.11/1.01  
% 2.11/1.01  ------ Propositional Solver
% 2.11/1.01  
% 2.11/1.01  prop_solver_calls:                      27
% 2.11/1.01  prop_fast_solver_calls:                 949
% 2.11/1.01  smt_solver_calls:                       0
% 2.11/1.01  smt_fast_solver_calls:                  0
% 2.11/1.01  prop_num_of_clauses:                    1077
% 2.11/1.01  prop_preprocess_simplified:             4291
% 2.11/1.01  prop_fo_subsumed:                       33
% 2.11/1.01  prop_solver_time:                       0.
% 2.11/1.01  smt_solver_time:                        0.
% 2.11/1.01  smt_fast_solver_time:                   0.
% 2.11/1.01  prop_fast_solver_time:                  0.
% 2.11/1.01  prop_unsat_core_time:                   0.
% 2.11/1.01  
% 2.11/1.01  ------ QBF
% 2.11/1.01  
% 2.11/1.01  qbf_q_res:                              0
% 2.11/1.01  qbf_num_tautologies:                    0
% 2.11/1.01  qbf_prep_cycles:                        0
% 2.11/1.01  
% 2.11/1.01  ------ BMC1
% 2.11/1.01  
% 2.11/1.01  bmc1_current_bound:                     -1
% 2.11/1.01  bmc1_last_solved_bound:                 -1
% 2.11/1.01  bmc1_unsat_core_size:                   -1
% 2.11/1.01  bmc1_unsat_core_parents_size:           -1
% 2.11/1.01  bmc1_merge_next_fun:                    0
% 2.11/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.11/1.01  
% 2.11/1.01  ------ Instantiation
% 2.11/1.01  
% 2.11/1.01  inst_num_of_clauses:                    283
% 2.11/1.01  inst_num_in_passive:                    95
% 2.11/1.01  inst_num_in_active:                     178
% 2.11/1.01  inst_num_in_unprocessed:                10
% 2.11/1.01  inst_num_of_loops:                      200
% 2.11/1.01  inst_num_of_learning_restarts:          0
% 2.11/1.01  inst_num_moves_active_passive:          19
% 2.11/1.01  inst_lit_activity:                      0
% 2.11/1.01  inst_lit_activity_moves:                0
% 2.11/1.01  inst_num_tautologies:                   0
% 2.11/1.01  inst_num_prop_implied:                  0
% 2.11/1.01  inst_num_existing_simplified:           0
% 2.11/1.01  inst_num_eq_res_simplified:             0
% 2.11/1.01  inst_num_child_elim:                    0
% 2.11/1.01  inst_num_of_dismatching_blockings:      38
% 2.11/1.01  inst_num_of_non_proper_insts:           218
% 2.11/1.01  inst_num_of_duplicates:                 0
% 2.11/1.01  inst_inst_num_from_inst_to_res:         0
% 2.11/1.01  inst_dismatching_checking_time:         0.
% 2.11/1.01  
% 2.11/1.01  ------ Resolution
% 2.11/1.01  
% 2.11/1.01  res_num_of_clauses:                     0
% 2.11/1.01  res_num_in_passive:                     0
% 2.11/1.01  res_num_in_active:                      0
% 2.11/1.01  res_num_of_loops:                       113
% 2.11/1.01  res_forward_subset_subsumed:            22
% 2.11/1.01  res_backward_subset_subsumed:           0
% 2.11/1.01  res_forward_subsumed:                   0
% 2.11/1.01  res_backward_subsumed:                  0
% 2.11/1.01  res_forward_subsumption_resolution:     1
% 2.11/1.01  res_backward_subsumption_resolution:    0
% 2.11/1.01  res_clause_to_clause_subsumption:       351
% 2.11/1.01  res_orphan_elimination:                 0
% 2.11/1.01  res_tautology_del:                      43
% 2.11/1.01  res_num_eq_res_simplified:              0
% 2.11/1.01  res_num_sel_changes:                    0
% 2.11/1.01  res_moves_from_active_to_pass:          0
% 2.11/1.01  
% 2.11/1.01  ------ Superposition
% 2.11/1.01  
% 2.11/1.01  sup_time_total:                         0.
% 2.11/1.01  sup_time_generating:                    0.
% 2.11/1.01  sup_time_sim_full:                      0.
% 2.11/1.01  sup_time_sim_immed:                     0.
% 2.11/1.01  
% 2.11/1.01  sup_num_of_clauses:                     67
% 2.11/1.01  sup_num_in_active:                      37
% 2.11/1.01  sup_num_in_passive:                     30
% 2.11/1.01  sup_num_of_loops:                       38
% 2.11/1.01  sup_fw_superposition:                   28
% 2.11/1.01  sup_bw_superposition:                   22
% 2.11/1.01  sup_immediate_simplified:               3
% 2.11/1.01  sup_given_eliminated:                   0
% 2.11/1.01  comparisons_done:                       0
% 2.11/1.01  comparisons_avoided:                    0
% 2.11/1.01  
% 2.11/1.01  ------ Simplifications
% 2.11/1.01  
% 2.11/1.01  
% 2.11/1.01  sim_fw_subset_subsumed:                 0
% 2.11/1.01  sim_bw_subset_subsumed:                 1
% 2.11/1.01  sim_fw_subsumed:                        1
% 2.11/1.01  sim_bw_subsumed:                        0
% 2.11/1.01  sim_fw_subsumption_res:                 0
% 2.11/1.01  sim_bw_subsumption_res:                 0
% 2.11/1.01  sim_tautology_del:                      2
% 2.11/1.01  sim_eq_tautology_del:                   1
% 2.11/1.01  sim_eq_res_simp:                        0
% 2.11/1.01  sim_fw_demodulated:                     0
% 2.11/1.01  sim_bw_demodulated:                     2
% 2.11/1.01  sim_light_normalised:                   2
% 2.11/1.01  sim_joinable_taut:                      0
% 2.11/1.01  sim_joinable_simp:                      0
% 2.11/1.01  sim_ac_normalised:                      0
% 2.11/1.01  sim_smt_subsumption:                    0
% 2.11/1.01  
%------------------------------------------------------------------------------

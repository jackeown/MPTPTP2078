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
% DateTime   : Thu Dec  3 12:15:09 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  150 (1197 expanded)
%              Number of clauses        :   96 ( 281 expanded)
%              Number of leaves         :   13 ( 299 expanded)
%              Depth                    :   26
%              Number of atoms          :  620 (11134 expanded)
%              Number of equality atoms :  177 (1907 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_286,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_287,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_291,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_20])).

cnf(c_292,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_441,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_292])).

cnf(c_442,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_18,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_514,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_tops_1(sK0,X0) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_442,c_18])).

cnf(c_1330,plain,
    ( v2_tops_1(sK1,sK0)
    | sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_514])).

cnf(c_1806,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1353,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_12,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_381,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_382,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_1975,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_1976,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_1981,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1982,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1981])).

cnf(c_1814,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_311,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_312,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_20])).

cnf(c_317,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_348,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_20])).

cnf(c_349,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_561,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_349])).

cnf(c_562,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_17])).

cnf(c_567,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_566])).

cnf(c_1327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_567])).

cnf(c_1804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_2067,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1804])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1810,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_2496,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1814,c_1810])).

cnf(c_1329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_tops_1(sK0,X0) != X0
    | k1_xboole_0 = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_514])).

cnf(c_1807,plain,
    ( k1_tops_1(sK0,X0) != X0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_1354,plain,
    ( k1_tops_1(sK0,X0) != X0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2015,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1818,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2251,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1818])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2272,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2951,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2272])).

cnf(c_2952,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2951])).

cnf(c_3244,plain,
    ( k1_xboole_0 = X0
    | k1_tops_1(sK0,X0) != X0
    | r1_tarski(X0,sK1) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1807,c_1354,c_2015,c_2251,c_2952])).

cnf(c_3245,plain,
    ( k1_tops_1(sK0,X0) != X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_3244])).

cnf(c_3254,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2496,c_3245])).

cnf(c_3335,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1806,c_24,c_1353,c_1976,c_1982,c_2067,c_3254])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_366,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_367,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_1813,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_2684,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1813])).

cnf(c_3341,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3335,c_2684])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_396,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_397,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_537,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_397])).

cnf(c_538,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_17])).

cnf(c_543,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_542])).

cnf(c_1805,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_2713,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1805])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1995,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1996,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1995])).

cnf(c_3219,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2713,c_24,c_29,c_1996])).

cnf(c_3220,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3219])).

cnf(c_3461,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3341,c_3220])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2226,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2229,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2226])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2030,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2031,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2030])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,plain,
    ( k1_xboole_0 != sK2
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3461,c_3335,c_2229,c_2031,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:45:30 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.34/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/0.98  
% 2.34/0.98  ------  iProver source info
% 2.34/0.98  
% 2.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/0.98  git: non_committed_changes: false
% 2.34/0.98  git: last_make_outside_of_git: false
% 2.34/0.98  
% 2.34/0.98  ------ 
% 2.34/0.98  
% 2.34/0.98  ------ Input Options
% 2.34/0.98  
% 2.34/0.98  --out_options                           all
% 2.34/0.98  --tptp_safe_out                         true
% 2.34/0.98  --problem_path                          ""
% 2.34/0.98  --include_path                          ""
% 2.34/0.98  --clausifier                            res/vclausify_rel
% 2.34/0.98  --clausifier_options                    --mode clausify
% 2.34/0.98  --stdin                                 false
% 2.34/0.98  --stats_out                             all
% 2.34/0.98  
% 2.34/0.98  ------ General Options
% 2.34/0.98  
% 2.34/0.98  --fof                                   false
% 2.34/0.98  --time_out_real                         305.
% 2.34/0.98  --time_out_virtual                      -1.
% 2.34/0.98  --symbol_type_check                     false
% 2.34/0.98  --clausify_out                          false
% 2.34/0.98  --sig_cnt_out                           false
% 2.34/0.98  --trig_cnt_out                          false
% 2.34/0.98  --trig_cnt_out_tolerance                1.
% 2.34/0.98  --trig_cnt_out_sk_spl                   false
% 2.34/0.98  --abstr_cl_out                          false
% 2.34/0.98  
% 2.34/0.98  ------ Global Options
% 2.34/0.98  
% 2.34/0.98  --schedule                              default
% 2.34/0.98  --add_important_lit                     false
% 2.34/0.98  --prop_solver_per_cl                    1000
% 2.34/0.98  --min_unsat_core                        false
% 2.34/0.98  --soft_assumptions                      false
% 2.34/0.98  --soft_lemma_size                       3
% 2.34/0.98  --prop_impl_unit_size                   0
% 2.34/0.98  --prop_impl_unit                        []
% 2.34/0.98  --share_sel_clauses                     true
% 2.34/0.98  --reset_solvers                         false
% 2.34/0.98  --bc_imp_inh                            [conj_cone]
% 2.34/0.98  --conj_cone_tolerance                   3.
% 2.34/0.98  --extra_neg_conj                        none
% 2.34/0.98  --large_theory_mode                     true
% 2.34/0.98  --prolific_symb_bound                   200
% 2.34/0.98  --lt_threshold                          2000
% 2.34/0.98  --clause_weak_htbl                      true
% 2.34/0.98  --gc_record_bc_elim                     false
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing Options
% 2.34/0.98  
% 2.34/0.98  --preprocessing_flag                    true
% 2.34/0.98  --time_out_prep_mult                    0.1
% 2.34/0.98  --splitting_mode                        input
% 2.34/0.98  --splitting_grd                         true
% 2.34/0.98  --splitting_cvd                         false
% 2.34/0.98  --splitting_cvd_svl                     false
% 2.34/0.98  --splitting_nvd                         32
% 2.34/0.98  --sub_typing                            true
% 2.34/0.98  --prep_gs_sim                           true
% 2.34/0.98  --prep_unflatten                        true
% 2.34/0.98  --prep_res_sim                          true
% 2.34/0.98  --prep_upred                            true
% 2.34/0.98  --prep_sem_filter                       exhaustive
% 2.34/0.98  --prep_sem_filter_out                   false
% 2.34/0.98  --pred_elim                             true
% 2.34/0.98  --res_sim_input                         true
% 2.34/0.98  --eq_ax_congr_red                       true
% 2.34/0.98  --pure_diseq_elim                       true
% 2.34/0.98  --brand_transform                       false
% 2.34/0.98  --non_eq_to_eq                          false
% 2.34/0.98  --prep_def_merge                        true
% 2.34/0.98  --prep_def_merge_prop_impl              false
% 2.34/0.98  --prep_def_merge_mbd                    true
% 2.34/0.98  --prep_def_merge_tr_red                 false
% 2.34/0.98  --prep_def_merge_tr_cl                  false
% 2.34/0.98  --smt_preprocessing                     true
% 2.34/0.98  --smt_ac_axioms                         fast
% 2.34/0.98  --preprocessed_out                      false
% 2.34/0.98  --preprocessed_stats                    false
% 2.34/0.98  
% 2.34/0.98  ------ Abstraction refinement Options
% 2.34/0.98  
% 2.34/0.98  --abstr_ref                             []
% 2.34/0.98  --abstr_ref_prep                        false
% 2.34/0.98  --abstr_ref_until_sat                   false
% 2.34/0.98  --abstr_ref_sig_restrict                funpre
% 2.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.98  --abstr_ref_under                       []
% 2.34/0.98  
% 2.34/0.98  ------ SAT Options
% 2.34/0.98  
% 2.34/0.98  --sat_mode                              false
% 2.34/0.98  --sat_fm_restart_options                ""
% 2.34/0.98  --sat_gr_def                            false
% 2.34/0.98  --sat_epr_types                         true
% 2.34/0.98  --sat_non_cyclic_types                  false
% 2.34/0.98  --sat_finite_models                     false
% 2.34/0.98  --sat_fm_lemmas                         false
% 2.34/0.98  --sat_fm_prep                           false
% 2.34/0.98  --sat_fm_uc_incr                        true
% 2.34/0.98  --sat_out_model                         small
% 2.34/0.98  --sat_out_clauses                       false
% 2.34/0.98  
% 2.34/0.98  ------ QBF Options
% 2.34/0.98  
% 2.34/0.98  --qbf_mode                              false
% 2.34/0.98  --qbf_elim_univ                         false
% 2.34/0.98  --qbf_dom_inst                          none
% 2.34/0.98  --qbf_dom_pre_inst                      false
% 2.34/0.98  --qbf_sk_in                             false
% 2.34/0.98  --qbf_pred_elim                         true
% 2.34/0.98  --qbf_split                             512
% 2.34/0.98  
% 2.34/0.98  ------ BMC1 Options
% 2.34/0.98  
% 2.34/0.98  --bmc1_incremental                      false
% 2.34/0.98  --bmc1_axioms                           reachable_all
% 2.34/0.98  --bmc1_min_bound                        0
% 2.34/0.98  --bmc1_max_bound                        -1
% 2.34/0.98  --bmc1_max_bound_default                -1
% 2.34/0.98  --bmc1_symbol_reachability              true
% 2.34/0.98  --bmc1_property_lemmas                  false
% 2.34/0.98  --bmc1_k_induction                      false
% 2.34/0.98  --bmc1_non_equiv_states                 false
% 2.34/0.98  --bmc1_deadlock                         false
% 2.34/0.98  --bmc1_ucm                              false
% 2.34/0.98  --bmc1_add_unsat_core                   none
% 2.34/0.98  --bmc1_unsat_core_children              false
% 2.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.98  --bmc1_out_stat                         full
% 2.34/0.98  --bmc1_ground_init                      false
% 2.34/0.98  --bmc1_pre_inst_next_state              false
% 2.34/0.98  --bmc1_pre_inst_state                   false
% 2.34/0.98  --bmc1_pre_inst_reach_state             false
% 2.34/0.98  --bmc1_out_unsat_core                   false
% 2.34/0.98  --bmc1_aig_witness_out                  false
% 2.34/0.98  --bmc1_verbose                          false
% 2.34/0.98  --bmc1_dump_clauses_tptp                false
% 2.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.98  --bmc1_dump_file                        -
% 2.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.98  --bmc1_ucm_extend_mode                  1
% 2.34/0.98  --bmc1_ucm_init_mode                    2
% 2.34/0.98  --bmc1_ucm_cone_mode                    none
% 2.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.98  --bmc1_ucm_relax_model                  4
% 2.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.98  --bmc1_ucm_layered_model                none
% 2.34/0.98  --bmc1_ucm_max_lemma_size               10
% 2.34/0.98  
% 2.34/0.98  ------ AIG Options
% 2.34/0.98  
% 2.34/0.98  --aig_mode                              false
% 2.34/0.98  
% 2.34/0.98  ------ Instantiation Options
% 2.34/0.98  
% 2.34/0.98  --instantiation_flag                    true
% 2.34/0.98  --inst_sos_flag                         false
% 2.34/0.98  --inst_sos_phase                        true
% 2.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.98  --inst_lit_sel_side                     num_symb
% 2.34/0.98  --inst_solver_per_active                1400
% 2.34/0.98  --inst_solver_calls_frac                1.
% 2.34/0.98  --inst_passive_queue_type               priority_queues
% 2.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.98  --inst_passive_queues_freq              [25;2]
% 2.34/0.98  --inst_dismatching                      true
% 2.34/0.98  --inst_eager_unprocessed_to_passive     true
% 2.34/0.98  --inst_prop_sim_given                   true
% 2.34/0.98  --inst_prop_sim_new                     false
% 2.34/0.98  --inst_subs_new                         false
% 2.34/0.98  --inst_eq_res_simp                      false
% 2.34/0.98  --inst_subs_given                       false
% 2.34/0.98  --inst_orphan_elimination               true
% 2.34/0.98  --inst_learning_loop_flag               true
% 2.34/0.98  --inst_learning_start                   3000
% 2.34/0.98  --inst_learning_factor                  2
% 2.34/0.98  --inst_start_prop_sim_after_learn       3
% 2.34/0.98  --inst_sel_renew                        solver
% 2.34/0.98  --inst_lit_activity_flag                true
% 2.34/0.98  --inst_restr_to_given                   false
% 2.34/0.98  --inst_activity_threshold               500
% 2.34/0.98  --inst_out_proof                        true
% 2.34/0.98  
% 2.34/0.98  ------ Resolution Options
% 2.34/0.98  
% 2.34/0.98  --resolution_flag                       true
% 2.34/0.98  --res_lit_sel                           adaptive
% 2.34/0.98  --res_lit_sel_side                      none
% 2.34/0.98  --res_ordering                          kbo
% 2.34/0.98  --res_to_prop_solver                    active
% 2.34/0.98  --res_prop_simpl_new                    false
% 2.34/0.98  --res_prop_simpl_given                  true
% 2.34/0.98  --res_passive_queue_type                priority_queues
% 2.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.98  --res_passive_queues_freq               [15;5]
% 2.34/0.98  --res_forward_subs                      full
% 2.34/0.98  --res_backward_subs                     full
% 2.34/0.98  --res_forward_subs_resolution           true
% 2.34/0.98  --res_backward_subs_resolution          true
% 2.34/0.98  --res_orphan_elimination                true
% 2.34/0.98  --res_time_limit                        2.
% 2.34/0.98  --res_out_proof                         true
% 2.34/0.98  
% 2.34/0.98  ------ Superposition Options
% 2.34/0.98  
% 2.34/0.98  --superposition_flag                    true
% 2.34/0.98  --sup_passive_queue_type                priority_queues
% 2.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.98  --demod_completeness_check              fast
% 2.34/0.98  --demod_use_ground                      true
% 2.34/0.98  --sup_to_prop_solver                    passive
% 2.34/0.98  --sup_prop_simpl_new                    true
% 2.34/0.98  --sup_prop_simpl_given                  true
% 2.34/0.98  --sup_fun_splitting                     false
% 2.34/0.98  --sup_smt_interval                      50000
% 2.34/0.98  
% 2.34/0.98  ------ Superposition Simplification Setup
% 2.34/0.98  
% 2.34/0.98  --sup_indices_passive                   []
% 2.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_full_bw                           [BwDemod]
% 2.34/0.98  --sup_immed_triv                        [TrivRules]
% 2.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_immed_bw_main                     []
% 2.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.98  
% 2.34/0.98  ------ Combination Options
% 2.34/0.98  
% 2.34/0.98  --comb_res_mult                         3
% 2.34/0.98  --comb_sup_mult                         2
% 2.34/0.98  --comb_inst_mult                        10
% 2.34/0.98  
% 2.34/0.98  ------ Debug Options
% 2.34/0.98  
% 2.34/0.98  --dbg_backtrace                         false
% 2.34/0.98  --dbg_dump_prop_clauses                 false
% 2.34/0.98  --dbg_dump_prop_clauses_file            -
% 2.34/0.98  --dbg_out_stat                          false
% 2.34/0.98  ------ Parsing...
% 2.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/0.98  ------ Proving...
% 2.34/0.98  ------ Problem Properties 
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  clauses                                 21
% 2.34/0.98  conjectures                             4
% 2.34/0.98  EPR                                     7
% 2.34/0.98  Horn                                    19
% 2.34/0.98  unary                                   3
% 2.34/0.98  binary                                  9
% 2.34/0.98  lits                                    53
% 2.34/0.98  lits eq                                 9
% 2.34/0.98  fd_pure                                 0
% 2.34/0.98  fd_pseudo                               0
% 2.34/0.98  fd_cond                                 1
% 2.34/0.98  fd_pseudo_cond                          1
% 2.34/0.98  AC symbols                              0
% 2.34/0.98  
% 2.34/0.98  ------ Schedule dynamic 5 is on 
% 2.34/0.98  
% 2.34/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  ------ 
% 2.34/0.98  Current options:
% 2.34/0.98  ------ 
% 2.34/0.98  
% 2.34/0.98  ------ Input Options
% 2.34/0.98  
% 2.34/0.98  --out_options                           all
% 2.34/0.98  --tptp_safe_out                         true
% 2.34/0.98  --problem_path                          ""
% 2.34/0.98  --include_path                          ""
% 2.34/0.98  --clausifier                            res/vclausify_rel
% 2.34/0.98  --clausifier_options                    --mode clausify
% 2.34/0.98  --stdin                                 false
% 2.34/0.98  --stats_out                             all
% 2.34/0.98  
% 2.34/0.98  ------ General Options
% 2.34/0.98  
% 2.34/0.98  --fof                                   false
% 2.34/0.98  --time_out_real                         305.
% 2.34/0.98  --time_out_virtual                      -1.
% 2.34/0.98  --symbol_type_check                     false
% 2.34/0.98  --clausify_out                          false
% 2.34/0.98  --sig_cnt_out                           false
% 2.34/0.98  --trig_cnt_out                          false
% 2.34/0.98  --trig_cnt_out_tolerance                1.
% 2.34/0.98  --trig_cnt_out_sk_spl                   false
% 2.34/0.98  --abstr_cl_out                          false
% 2.34/0.98  
% 2.34/0.98  ------ Global Options
% 2.34/0.98  
% 2.34/0.98  --schedule                              default
% 2.34/0.98  --add_important_lit                     false
% 2.34/0.98  --prop_solver_per_cl                    1000
% 2.34/0.98  --min_unsat_core                        false
% 2.34/0.98  --soft_assumptions                      false
% 2.34/0.98  --soft_lemma_size                       3
% 2.34/0.98  --prop_impl_unit_size                   0
% 2.34/0.98  --prop_impl_unit                        []
% 2.34/0.98  --share_sel_clauses                     true
% 2.34/0.98  --reset_solvers                         false
% 2.34/0.98  --bc_imp_inh                            [conj_cone]
% 2.34/0.98  --conj_cone_tolerance                   3.
% 2.34/0.98  --extra_neg_conj                        none
% 2.34/0.98  --large_theory_mode                     true
% 2.34/0.98  --prolific_symb_bound                   200
% 2.34/0.98  --lt_threshold                          2000
% 2.34/0.98  --clause_weak_htbl                      true
% 2.34/0.98  --gc_record_bc_elim                     false
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing Options
% 2.34/0.98  
% 2.34/0.98  --preprocessing_flag                    true
% 2.34/0.98  --time_out_prep_mult                    0.1
% 2.34/0.98  --splitting_mode                        input
% 2.34/0.98  --splitting_grd                         true
% 2.34/0.98  --splitting_cvd                         false
% 2.34/0.98  --splitting_cvd_svl                     false
% 2.34/0.98  --splitting_nvd                         32
% 2.34/0.98  --sub_typing                            true
% 2.34/0.98  --prep_gs_sim                           true
% 2.34/0.98  --prep_unflatten                        true
% 2.34/0.98  --prep_res_sim                          true
% 2.34/0.98  --prep_upred                            true
% 2.34/0.98  --prep_sem_filter                       exhaustive
% 2.34/0.98  --prep_sem_filter_out                   false
% 2.34/0.98  --pred_elim                             true
% 2.34/0.98  --res_sim_input                         true
% 2.34/0.98  --eq_ax_congr_red                       true
% 2.34/0.98  --pure_diseq_elim                       true
% 2.34/0.98  --brand_transform                       false
% 2.34/0.98  --non_eq_to_eq                          false
% 2.34/0.98  --prep_def_merge                        true
% 2.34/0.98  --prep_def_merge_prop_impl              false
% 2.34/0.98  --prep_def_merge_mbd                    true
% 2.34/0.98  --prep_def_merge_tr_red                 false
% 2.34/0.98  --prep_def_merge_tr_cl                  false
% 2.34/0.98  --smt_preprocessing                     true
% 2.34/0.98  --smt_ac_axioms                         fast
% 2.34/0.98  --preprocessed_out                      false
% 2.34/0.98  --preprocessed_stats                    false
% 2.34/0.98  
% 2.34/0.98  ------ Abstraction refinement Options
% 2.34/0.98  
% 2.34/0.98  --abstr_ref                             []
% 2.34/0.98  --abstr_ref_prep                        false
% 2.34/0.98  --abstr_ref_until_sat                   false
% 2.34/0.98  --abstr_ref_sig_restrict                funpre
% 2.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.98  --abstr_ref_under                       []
% 2.34/0.98  
% 2.34/0.98  ------ SAT Options
% 2.34/0.98  
% 2.34/0.98  --sat_mode                              false
% 2.34/0.98  --sat_fm_restart_options                ""
% 2.34/0.98  --sat_gr_def                            false
% 2.34/0.98  --sat_epr_types                         true
% 2.34/0.98  --sat_non_cyclic_types                  false
% 2.34/0.98  --sat_finite_models                     false
% 2.34/0.98  --sat_fm_lemmas                         false
% 2.34/0.98  --sat_fm_prep                           false
% 2.34/0.98  --sat_fm_uc_incr                        true
% 2.34/0.98  --sat_out_model                         small
% 2.34/0.98  --sat_out_clauses                       false
% 2.34/0.98  
% 2.34/0.98  ------ QBF Options
% 2.34/0.98  
% 2.34/0.98  --qbf_mode                              false
% 2.34/0.98  --qbf_elim_univ                         false
% 2.34/0.98  --qbf_dom_inst                          none
% 2.34/0.98  --qbf_dom_pre_inst                      false
% 2.34/0.98  --qbf_sk_in                             false
% 2.34/0.98  --qbf_pred_elim                         true
% 2.34/0.98  --qbf_split                             512
% 2.34/0.98  
% 2.34/0.98  ------ BMC1 Options
% 2.34/0.98  
% 2.34/0.98  --bmc1_incremental                      false
% 2.34/0.98  --bmc1_axioms                           reachable_all
% 2.34/0.98  --bmc1_min_bound                        0
% 2.34/0.98  --bmc1_max_bound                        -1
% 2.34/0.98  --bmc1_max_bound_default                -1
% 2.34/0.98  --bmc1_symbol_reachability              true
% 2.34/0.98  --bmc1_property_lemmas                  false
% 2.34/0.98  --bmc1_k_induction                      false
% 2.34/0.98  --bmc1_non_equiv_states                 false
% 2.34/0.98  --bmc1_deadlock                         false
% 2.34/0.98  --bmc1_ucm                              false
% 2.34/0.98  --bmc1_add_unsat_core                   none
% 2.34/0.98  --bmc1_unsat_core_children              false
% 2.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.98  --bmc1_out_stat                         full
% 2.34/0.98  --bmc1_ground_init                      false
% 2.34/0.98  --bmc1_pre_inst_next_state              false
% 2.34/0.98  --bmc1_pre_inst_state                   false
% 2.34/0.98  --bmc1_pre_inst_reach_state             false
% 2.34/0.98  --bmc1_out_unsat_core                   false
% 2.34/0.98  --bmc1_aig_witness_out                  false
% 2.34/0.98  --bmc1_verbose                          false
% 2.34/0.98  --bmc1_dump_clauses_tptp                false
% 2.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.98  --bmc1_dump_file                        -
% 2.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.98  --bmc1_ucm_extend_mode                  1
% 2.34/0.98  --bmc1_ucm_init_mode                    2
% 2.34/0.98  --bmc1_ucm_cone_mode                    none
% 2.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.98  --bmc1_ucm_relax_model                  4
% 2.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.98  --bmc1_ucm_layered_model                none
% 2.34/0.98  --bmc1_ucm_max_lemma_size               10
% 2.34/0.98  
% 2.34/0.98  ------ AIG Options
% 2.34/0.98  
% 2.34/0.98  --aig_mode                              false
% 2.34/0.98  
% 2.34/0.98  ------ Instantiation Options
% 2.34/0.98  
% 2.34/0.98  --instantiation_flag                    true
% 2.34/0.98  --inst_sos_flag                         false
% 2.34/0.98  --inst_sos_phase                        true
% 2.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.98  --inst_lit_sel_side                     none
% 2.34/0.98  --inst_solver_per_active                1400
% 2.34/0.98  --inst_solver_calls_frac                1.
% 2.34/0.98  --inst_passive_queue_type               priority_queues
% 2.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.98  --inst_passive_queues_freq              [25;2]
% 2.34/0.98  --inst_dismatching                      true
% 2.34/0.98  --inst_eager_unprocessed_to_passive     true
% 2.34/0.98  --inst_prop_sim_given                   true
% 2.34/0.98  --inst_prop_sim_new                     false
% 2.34/0.98  --inst_subs_new                         false
% 2.34/0.98  --inst_eq_res_simp                      false
% 2.34/0.98  --inst_subs_given                       false
% 2.34/0.98  --inst_orphan_elimination               true
% 2.34/0.98  --inst_learning_loop_flag               true
% 2.34/0.98  --inst_learning_start                   3000
% 2.34/0.98  --inst_learning_factor                  2
% 2.34/0.98  --inst_start_prop_sim_after_learn       3
% 2.34/0.98  --inst_sel_renew                        solver
% 2.34/0.98  --inst_lit_activity_flag                true
% 2.34/0.98  --inst_restr_to_given                   false
% 2.34/0.98  --inst_activity_threshold               500
% 2.34/0.98  --inst_out_proof                        true
% 2.34/0.98  
% 2.34/0.98  ------ Resolution Options
% 2.34/0.98  
% 2.34/0.98  --resolution_flag                       false
% 2.34/0.98  --res_lit_sel                           adaptive
% 2.34/0.98  --res_lit_sel_side                      none
% 2.34/0.98  --res_ordering                          kbo
% 2.34/0.98  --res_to_prop_solver                    active
% 2.34/0.98  --res_prop_simpl_new                    false
% 2.34/0.98  --res_prop_simpl_given                  true
% 2.34/0.98  --res_passive_queue_type                priority_queues
% 2.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.98  --res_passive_queues_freq               [15;5]
% 2.34/0.98  --res_forward_subs                      full
% 2.34/0.98  --res_backward_subs                     full
% 2.34/0.98  --res_forward_subs_resolution           true
% 2.34/0.98  --res_backward_subs_resolution          true
% 2.34/0.98  --res_orphan_elimination                true
% 2.34/0.98  --res_time_limit                        2.
% 2.34/0.98  --res_out_proof                         true
% 2.34/0.98  
% 2.34/0.98  ------ Superposition Options
% 2.34/0.98  
% 2.34/0.98  --superposition_flag                    true
% 2.34/0.98  --sup_passive_queue_type                priority_queues
% 2.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.98  --demod_completeness_check              fast
% 2.34/0.98  --demod_use_ground                      true
% 2.34/0.98  --sup_to_prop_solver                    passive
% 2.34/0.98  --sup_prop_simpl_new                    true
% 2.34/0.98  --sup_prop_simpl_given                  true
% 2.34/0.98  --sup_fun_splitting                     false
% 2.34/0.98  --sup_smt_interval                      50000
% 2.34/0.98  
% 2.34/0.98  ------ Superposition Simplification Setup
% 2.34/0.98  
% 2.34/0.98  --sup_indices_passive                   []
% 2.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_full_bw                           [BwDemod]
% 2.34/0.98  --sup_immed_triv                        [TrivRules]
% 2.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_immed_bw_main                     []
% 2.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.98  
% 2.34/0.98  ------ Combination Options
% 2.34/0.98  
% 2.34/0.98  --comb_res_mult                         3
% 2.34/0.98  --comb_sup_mult                         2
% 2.34/0.98  --comb_inst_mult                        10
% 2.34/0.98  
% 2.34/0.98  ------ Debug Options
% 2.34/0.98  
% 2.34/0.98  --dbg_backtrace                         false
% 2.34/0.98  --dbg_dump_prop_clauses                 false
% 2.34/0.98  --dbg_dump_prop_clauses_file            -
% 2.34/0.98  --dbg_out_stat                          false
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  ------ Proving...
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  % SZS status Theorem for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  fof(f10,conjecture,(
% 2.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f11,negated_conjecture,(
% 2.34/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.34/0.98    inference(negated_conjecture,[],[f10])).
% 2.34/0.98  
% 2.34/0.98  fof(f22,plain,(
% 2.34/0.98    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.34/0.98    inference(ennf_transformation,[],[f11])).
% 2.34/0.98  
% 2.34/0.98  fof(f23,plain,(
% 2.34/0.98    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.34/0.98    inference(flattening,[],[f22])).
% 2.34/0.98  
% 2.34/0.98  fof(f28,plain,(
% 2.34/0.98    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.34/0.98    inference(nnf_transformation,[],[f23])).
% 2.34/0.98  
% 2.34/0.98  fof(f29,plain,(
% 2.34/0.98    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.34/0.98    inference(flattening,[],[f28])).
% 2.34/0.98  
% 2.34/0.98  fof(f30,plain,(
% 2.34/0.98    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.34/0.98    inference(rectify,[],[f29])).
% 2.34/0.98  
% 2.34/0.98  fof(f33,plain,(
% 2.34/0.98    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.34/0.98    introduced(choice_axiom,[])).
% 2.34/0.98  
% 2.34/0.98  fof(f32,plain,(
% 2.34/0.98    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.34/0.98    introduced(choice_axiom,[])).
% 2.34/0.98  
% 2.34/0.98  fof(f31,plain,(
% 2.34/0.98    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.34/0.98    introduced(choice_axiom,[])).
% 2.34/0.98  
% 2.34/0.98  fof(f34,plain,(
% 2.34/0.98    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).
% 2.34/0.98  
% 2.34/0.98  fof(f50,plain,(
% 2.34/0.98    l1_pre_topc(sK0)),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f7,axiom,(
% 2.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f17,plain,(
% 2.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.34/0.98    inference(ennf_transformation,[],[f7])).
% 2.34/0.98  
% 2.34/0.98  fof(f18,plain,(
% 2.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.34/0.98    inference(flattening,[],[f17])).
% 2.34/0.98  
% 2.34/0.98  fof(f45,plain,(
% 2.34/0.98    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f18])).
% 2.34/0.98  
% 2.34/0.98  fof(f49,plain,(
% 2.34/0.98    v2_pre_topc(sK0)),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f52,plain,(
% 2.34/0.98    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f51,plain,(
% 2.34/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f9,axiom,(
% 2.34/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f21,plain,(
% 2.34/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.34/0.98    inference(ennf_transformation,[],[f9])).
% 2.34/0.98  
% 2.34/0.98  fof(f27,plain,(
% 2.34/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.34/0.98    inference(nnf_transformation,[],[f21])).
% 2.34/0.98  
% 2.34/0.98  fof(f48,plain,(
% 2.34/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f27])).
% 2.34/0.98  
% 2.34/0.98  fof(f6,axiom,(
% 2.34/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f16,plain,(
% 2.34/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.34/0.98    inference(ennf_transformation,[],[f6])).
% 2.34/0.98  
% 2.34/0.98  fof(f43,plain,(
% 2.34/0.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f16])).
% 2.34/0.98  
% 2.34/0.98  fof(f55,plain,(
% 2.34/0.98    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f44,plain,(
% 2.34/0.98    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f18])).
% 2.34/0.98  
% 2.34/0.98  fof(f53,plain,(
% 2.34/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f5,axiom,(
% 2.34/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f14,plain,(
% 2.34/0.98    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.34/0.98    inference(ennf_transformation,[],[f5])).
% 2.34/0.98  
% 2.34/0.98  fof(f15,plain,(
% 2.34/0.98    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.34/0.98    inference(flattening,[],[f14])).
% 2.34/0.98  
% 2.34/0.98  fof(f42,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f15])).
% 2.34/0.98  
% 2.34/0.98  fof(f4,axiom,(
% 2.34/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f26,plain,(
% 2.34/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.34/0.98    inference(nnf_transformation,[],[f4])).
% 2.34/0.98  
% 2.34/0.98  fof(f41,plain,(
% 2.34/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f26])).
% 2.34/0.98  
% 2.34/0.98  fof(f40,plain,(
% 2.34/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.34/0.98    inference(cnf_transformation,[],[f26])).
% 2.34/0.98  
% 2.34/0.98  fof(f2,axiom,(
% 2.34/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f12,plain,(
% 2.34/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.34/0.98    inference(ennf_transformation,[],[f2])).
% 2.34/0.98  
% 2.34/0.98  fof(f13,plain,(
% 2.34/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.34/0.98    inference(flattening,[],[f12])).
% 2.34/0.98  
% 2.34/0.98  fof(f38,plain,(
% 2.34/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f13])).
% 2.34/0.98  
% 2.34/0.98  fof(f47,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f27])).
% 2.34/0.98  
% 2.34/0.98  fof(f8,axiom,(
% 2.34/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f19,plain,(
% 2.34/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.34/0.98    inference(ennf_transformation,[],[f8])).
% 2.34/0.98  
% 2.34/0.98  fof(f20,plain,(
% 2.34/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.34/0.98    inference(flattening,[],[f19])).
% 2.34/0.98  
% 2.34/0.98  fof(f46,plain,(
% 2.34/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f20])).
% 2.34/0.98  
% 2.34/0.98  fof(f54,plain,(
% 2.34/0.98    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f3,axiom,(
% 2.34/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f39,plain,(
% 2.34/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f3])).
% 2.34/0.98  
% 2.34/0.98  fof(f1,axiom,(
% 2.34/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f24,plain,(
% 2.34/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/0.98    inference(nnf_transformation,[],[f1])).
% 2.34/0.98  
% 2.34/0.98  fof(f25,plain,(
% 2.34/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/0.98    inference(flattening,[],[f24])).
% 2.34/0.98  
% 2.34/0.98  fof(f37,plain,(
% 2.34/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f25])).
% 2.34/0.98  
% 2.34/0.98  fof(f56,plain,(
% 2.34/0.98    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  cnf(c_20,negated_conjecture,
% 2.34/0.98      ( l1_pre_topc(sK0) ),
% 2.34/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_9,plain,
% 2.34/0.98      ( v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ v2_pre_topc(X1)
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | ~ l1_pre_topc(X3)
% 2.34/0.98      | k1_tops_1(X1,X0) != X0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_21,negated_conjecture,
% 2.34/0.98      ( v2_pre_topc(sK0) ),
% 2.34/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_286,plain,
% 2.34/0.98      ( v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | ~ l1_pre_topc(X3)
% 2.34/0.98      | k1_tops_1(X1,X0) != X0
% 2.34/0.98      | sK0 != X1 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_287,plain,
% 2.34/0.98      ( v3_pre_topc(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ l1_pre_topc(X2)
% 2.34/0.98      | ~ l1_pre_topc(sK0)
% 2.34/0.98      | k1_tops_1(sK0,X0) != X0 ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_286]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_291,plain,
% 2.34/0.98      ( ~ l1_pre_topc(X2)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/0.98      | v3_pre_topc(X0,sK0)
% 2.34/0.98      | k1_tops_1(sK0,X0) != X0 ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_287,c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_292,plain,
% 2.34/0.98      ( v3_pre_topc(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ l1_pre_topc(X2)
% 2.34/0.98      | k1_tops_1(sK0,X0) != X0 ),
% 2.34/0.98      inference(renaming,[status(thm)],[c_291]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_441,plain,
% 2.34/0.98      ( v3_pre_topc(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,X0) != X0
% 2.34/0.98      | sK0 != X2 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_292]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_442,plain,
% 2.34/0.98      ( v3_pre_topc(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,X0) != X0 ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_441]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_18,negated_conjecture,
% 2.34/0.98      ( v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ v3_pre_topc(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ r1_tarski(X0,sK1)
% 2.34/0.98      | k1_xboole_0 = X0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_514,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ r1_tarski(X0,sK1)
% 2.34/0.98      | k1_tops_1(sK0,X0) != X0
% 2.34/0.98      | k1_xboole_0 = X0 ),
% 2.34/0.98      inference(resolution,[status(thm)],[c_442,c_18]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1330,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) | sP1_iProver_split | sP0_iProver_split ),
% 2.34/0.98      inference(splitting,
% 2.34/0.98                [splitting(split),new_symbols(definition,[])],
% 2.34/0.98                [c_514]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1806,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) = iProver_top
% 2.34/0.98      | sP1_iProver_split = iProver_top
% 2.34/0.98      | sP0_iProver_split = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_19,negated_conjecture,
% 2.34/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.34/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_24,plain,
% 2.34/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1353,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) = iProver_top
% 2.34/0.98      | sP1_iProver_split = iProver_top
% 2.34/0.98      | sP0_iProver_split = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_12,plain,
% 2.34/0.98      ( v2_tops_1(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_381,plain,
% 2.34/0.98      ( v2_tops_1(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.34/0.98      | sK0 != X1 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_382,plain,
% 2.34/0.98      ( v2_tops_1(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_381]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1975,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_382]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1976,plain,
% 2.34/0.98      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.34/0.98      | v2_tops_1(sK1,sK0) = iProver_top
% 2.34/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1975]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_8,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.34/0.98      | ~ l1_pre_topc(X1) ),
% 2.34/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_417,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.34/0.98      | sK0 != X1 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_418,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_417]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1981,plain,
% 2.34/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_418]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1982,plain,
% 2.34/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.34/0.98      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1981]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1814,plain,
% 2.34/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_15,negated_conjecture,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.34/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_10,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.34/0.98      | ~ v2_pre_topc(X3)
% 2.34/0.98      | ~ l1_pre_topc(X3)
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_311,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | ~ l1_pre_topc(X3)
% 2.34/0.98      | k1_tops_1(X1,X0) = X0
% 2.34/0.98      | sK0 != X3 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_312,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | ~ l1_pre_topc(sK0)
% 2.34/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_311]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_316,plain,
% 2.34/0.98      ( ~ l1_pre_topc(X1)
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ v3_pre_topc(X0,X1)
% 2.34/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_312,c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_317,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.34/0.98      inference(renaming,[status(thm)],[c_316]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_348,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(X1,X0) = X0
% 2.34/0.98      | sK0 != X1 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_317,c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_349,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,X0) = X0 ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_348]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_561,plain,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,X0) = X0
% 2.34/0.98      | sK0 != sK0
% 2.34/0.98      | sK2 != X0 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_349]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_562,plain,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,sK2) = sK2 ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_561]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_17,negated_conjecture,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.34/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_566,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | k1_tops_1(sK0,sK2) = sK2 ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_562,c_17]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_567,plain,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,sK2) = sK2 ),
% 2.34/0.98      inference(renaming,[status(thm)],[c_566]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1327,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ sP0_iProver_split ),
% 2.34/0.98      inference(splitting,
% 2.34/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.34/0.98                [c_567]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1804,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.34/0.98      | sP0_iProver_split != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1327]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2067,plain,
% 2.34/0.98      ( sP0_iProver_split != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1814,c_1804]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_7,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 2.34/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_429,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 2.34/0.98      | sK0 != X1 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_430,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_429]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1810,plain,
% 2.34/0.98      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 2.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2496,plain,
% 2.34/0.98      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1814,c_1810]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1329,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ r1_tarski(X0,sK1)
% 2.34/0.98      | k1_tops_1(sK0,X0) != X0
% 2.34/0.98      | k1_xboole_0 = X0
% 2.34/0.98      | ~ sP1_iProver_split ),
% 2.34/0.98      inference(splitting,
% 2.34/0.98                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.34/0.98                [c_514]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1807,plain,
% 2.34/0.98      ( k1_tops_1(sK0,X0) != X0
% 2.34/0.98      | k1_xboole_0 = X0
% 2.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.34/0.98      | r1_tarski(X0,sK1) != iProver_top
% 2.34/0.98      | sP1_iProver_split != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1329]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1354,plain,
% 2.34/0.98      ( k1_tops_1(sK0,X0) != X0
% 2.34/0.98      | k1_xboole_0 = X0
% 2.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.34/0.98      | r1_tarski(X0,sK1) != iProver_top
% 2.34/0.98      | sP1_iProver_split != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1329]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_5,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.34/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2014,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2015,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.34/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2014]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_6,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.34/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1818,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.34/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2251,plain,
% 2.34/0.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1814,c_1818]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3,plain,
% 2.34/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.34/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2272,plain,
% 2.34/0.98      ( ~ r1_tarski(X0,X1)
% 2.34/0.98      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 2.34/0.98      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2951,plain,
% 2.34/0.98      ( r1_tarski(X0,u1_struct_0(sK0))
% 2.34/0.98      | ~ r1_tarski(X0,sK1)
% 2.34/0.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_2272]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2952,plain,
% 2.34/0.98      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 2.34/0.98      | r1_tarski(X0,sK1) != iProver_top
% 2.34/0.98      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2951]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3244,plain,
% 2.34/0.98      ( k1_xboole_0 = X0
% 2.34/0.98      | k1_tops_1(sK0,X0) != X0
% 2.34/0.98      | r1_tarski(X0,sK1) != iProver_top
% 2.34/0.98      | sP1_iProver_split != iProver_top ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_1807,c_1354,c_2015,c_2251,c_2952]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3245,plain,
% 2.34/0.98      ( k1_tops_1(sK0,X0) != X0
% 2.34/0.98      | k1_xboole_0 = X0
% 2.34/0.98      | r1_tarski(X0,sK1) != iProver_top
% 2.34/0.98      | sP1_iProver_split != iProver_top ),
% 2.34/0.98      inference(renaming,[status(thm)],[c_3244]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3254,plain,
% 2.34/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.34/0.98      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 2.34/0.98      | sP1_iProver_split != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_2496,c_3245]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3335,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_1806,c_24,c_1353,c_1976,c_1982,c_2067,c_3254]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_13,plain,
% 2.34/0.98      ( ~ v2_tops_1(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ l1_pre_topc(X1)
% 2.34/0.98      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_366,plain,
% 2.34/0.98      ( ~ v2_tops_1(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.34/0.98      | sK0 != X1 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_367,plain,
% 2.34/0.98      ( ~ v2_tops_1(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_366]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1813,plain,
% 2.34/0.98      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.34/0.98      | v2_tops_1(X0,sK0) != iProver_top
% 2.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2684,plain,
% 2.34/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.34/0.98      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1814,c_1813]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3341,plain,
% 2.34/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_3335,c_2684]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_11,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ r1_tarski(X0,X2)
% 2.34/0.98      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.34/0.98      | ~ l1_pre_topc(X1) ),
% 2.34/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_396,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/0.98      | ~ r1_tarski(X0,X2)
% 2.34/0.98      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.34/0.98      | sK0 != X1 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_397,plain,
% 2.34/0.98      ( ~ v3_pre_topc(X0,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ r1_tarski(X0,X1)
% 2.34/0.98      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_396]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_537,plain,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ r1_tarski(X0,X1)
% 2.34/0.98      | r1_tarski(X0,k1_tops_1(sK0,X1))
% 2.34/0.98      | sK0 != sK0
% 2.34/0.98      | sK2 != X0 ),
% 2.34/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_397]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_538,plain,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ r1_tarski(sK2,X0)
% 2.34/0.98      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.34/0.98      inference(unflattening,[status(thm)],[c_537]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_542,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ r1_tarski(sK2,X0)
% 2.34/0.98      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_538,c_17]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_543,plain,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | ~ r1_tarski(sK2,X0)
% 2.34/0.98      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.34/0.98      inference(renaming,[status(thm)],[c_542]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1805,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.34/0.98      | r1_tarski(sK2,X0) != iProver_top
% 2.34/0.98      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2713,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.34/0.98      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.34/0.98      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1814,c_1805]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_16,negated_conjecture,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.34/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_29,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.34/0.98      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1995,plain,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0)
% 2.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.34/0.98      | r1_tarski(sK2,k1_tops_1(sK0,sK1))
% 2.34/0.98      | ~ r1_tarski(sK2,sK1) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_543]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1996,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.34/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.34/0.98      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.34/0.98      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1995]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3219,plain,
% 2.34/0.98      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.34/0.98      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_2713,c_24,c_29,c_1996]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3220,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.34/0.98      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.34/0.98      inference(renaming,[status(thm)],[c_3219]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3461,plain,
% 2.34/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.34/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.34/0.98      inference(demodulation,[status(thm)],[c_3341,c_3220]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_4,plain,
% 2.34/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.34/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2226,plain,
% 2.34/0.98      ( r1_tarski(k1_xboole_0,sK2) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2229,plain,
% 2.34/0.98      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2226]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_0,plain,
% 2.34/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.34/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2030,plain,
% 2.34/0.98      ( ~ r1_tarski(sK2,k1_xboole_0)
% 2.34/0.98      | ~ r1_tarski(k1_xboole_0,sK2)
% 2.34/0.98      | k1_xboole_0 = sK2 ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2031,plain,
% 2.34/0.98      ( k1_xboole_0 = sK2
% 2.34/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 2.34/0.98      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2030]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_14,negated_conjecture,
% 2.34/0.98      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.34/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_31,plain,
% 2.34/0.98      ( k1_xboole_0 != sK2 | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(contradiction,plain,
% 2.34/0.98      ( $false ),
% 2.34/0.98      inference(minisat,[status(thm)],[c_3461,c_3335,c_2229,c_2031,c_31]) ).
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  ------                               Statistics
% 2.34/0.98  
% 2.34/0.98  ------ General
% 2.34/0.98  
% 2.34/0.98  abstr_ref_over_cycles:                  0
% 2.34/0.98  abstr_ref_under_cycles:                 0
% 2.34/0.98  gc_basic_clause_elim:                   0
% 2.34/0.98  forced_gc_time:                         0
% 2.34/0.98  parsing_time:                           0.01
% 2.34/0.98  unif_index_cands_time:                  0.
% 2.34/0.98  unif_index_add_time:                    0.
% 2.34/0.98  orderings_time:                         0.
% 2.34/0.98  out_proof_time:                         0.009
% 2.34/0.98  total_time:                             0.115
% 2.34/0.98  num_of_symbols:                         46
% 2.34/0.98  num_of_terms:                           1407
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing
% 2.34/0.98  
% 2.34/0.98  num_of_splits:                          3
% 2.34/0.98  num_of_split_atoms:                     2
% 2.34/0.98  num_of_reused_defs:                     1
% 2.34/0.98  num_eq_ax_congr_red:                    1
% 2.34/0.98  num_of_sem_filtered_clauses:            1
% 2.34/0.98  num_of_subtypes:                        0
% 2.34/0.98  monotx_restored_types:                  0
% 2.34/0.98  sat_num_of_epr_types:                   0
% 2.34/0.98  sat_num_of_non_cyclic_types:            0
% 2.34/0.98  sat_guarded_non_collapsed_types:        0
% 2.34/0.98  num_pure_diseq_elim:                    0
% 2.34/0.98  simp_replaced_by:                       0
% 2.34/0.98  res_preprocessed:                       96
% 2.34/0.98  prep_upred:                             0
% 2.34/0.98  prep_unflattend:                        24
% 2.34/0.98  smt_new_axioms:                         0
% 2.34/0.98  pred_elim_cands:                        3
% 2.34/0.98  pred_elim:                              3
% 2.34/0.98  pred_elim_cl:                           3
% 2.34/0.98  pred_elim_cycles:                       5
% 2.34/0.98  merged_defs:                            8
% 2.34/0.98  merged_defs_ncl:                        0
% 2.34/0.98  bin_hyper_res:                          8
% 2.34/0.98  prep_cycles:                            4
% 2.34/0.98  pred_elim_time:                         0.017
% 2.34/0.98  splitting_time:                         0.
% 2.34/0.98  sem_filter_time:                        0.
% 2.34/0.98  monotx_time:                            0.
% 2.34/0.98  subtype_inf_time:                       0.
% 2.34/0.98  
% 2.34/0.98  ------ Problem properties
% 2.34/0.98  
% 2.34/0.98  clauses:                                21
% 2.34/0.98  conjectures:                            4
% 2.34/0.98  epr:                                    7
% 2.34/0.98  horn:                                   19
% 2.34/0.98  ground:                                 6
% 2.34/0.98  unary:                                  3
% 2.34/0.98  binary:                                 9
% 2.34/0.98  lits:                                   53
% 2.34/0.98  lits_eq:                                9
% 2.34/0.98  fd_pure:                                0
% 2.34/0.98  fd_pseudo:                              0
% 2.34/0.98  fd_cond:                                1
% 2.34/0.98  fd_pseudo_cond:                         1
% 2.34/0.98  ac_symbols:                             0
% 2.34/0.98  
% 2.34/0.98  ------ Propositional Solver
% 2.34/0.98  
% 2.34/0.98  prop_solver_calls:                      27
% 2.34/0.98  prop_fast_solver_calls:                 845
% 2.34/0.98  smt_solver_calls:                       0
% 2.34/0.98  smt_fast_solver_calls:                  0
% 2.34/0.98  prop_num_of_clauses:                    924
% 2.34/0.98  prop_preprocess_simplified:             3694
% 2.34/0.98  prop_fo_subsumed:                       25
% 2.34/0.98  prop_solver_time:                       0.
% 2.34/0.98  smt_solver_time:                        0.
% 2.34/0.98  smt_fast_solver_time:                   0.
% 2.34/0.98  prop_fast_solver_time:                  0.
% 2.34/0.98  prop_unsat_core_time:                   0.
% 2.34/0.98  
% 2.34/0.98  ------ QBF
% 2.34/0.98  
% 2.34/0.98  qbf_q_res:                              0
% 2.34/0.98  qbf_num_tautologies:                    0
% 2.34/0.98  qbf_prep_cycles:                        0
% 2.34/0.98  
% 2.34/0.98  ------ BMC1
% 2.34/0.98  
% 2.34/0.98  bmc1_current_bound:                     -1
% 2.34/0.98  bmc1_last_solved_bound:                 -1
% 2.34/0.98  bmc1_unsat_core_size:                   -1
% 2.34/0.98  bmc1_unsat_core_parents_size:           -1
% 2.34/0.98  bmc1_merge_next_fun:                    0
% 2.34/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.34/0.98  
% 2.34/0.98  ------ Instantiation
% 2.34/0.98  
% 2.34/0.98  inst_num_of_clauses:                    252
% 2.34/0.98  inst_num_in_passive:                    61
% 2.34/0.98  inst_num_in_active:                     157
% 2.34/0.98  inst_num_in_unprocessed:                34
% 2.34/0.98  inst_num_of_loops:                      170
% 2.34/0.98  inst_num_of_learning_restarts:          0
% 2.34/0.98  inst_num_moves_active_passive:          10
% 2.34/0.98  inst_lit_activity:                      0
% 2.34/0.98  inst_lit_activity_moves:                0
% 2.34/0.98  inst_num_tautologies:                   0
% 2.34/0.98  inst_num_prop_implied:                  0
% 2.34/0.98  inst_num_existing_simplified:           0
% 2.34/0.98  inst_num_eq_res_simplified:             0
% 2.34/0.98  inst_num_child_elim:                    0
% 2.34/0.98  inst_num_of_dismatching_blockings:      53
% 2.34/0.98  inst_num_of_non_proper_insts:           345
% 2.34/0.98  inst_num_of_duplicates:                 0
% 2.34/0.98  inst_inst_num_from_inst_to_res:         0
% 2.34/0.98  inst_dismatching_checking_time:         0.
% 2.34/0.98  
% 2.34/0.98  ------ Resolution
% 2.34/0.98  
% 2.34/0.98  res_num_of_clauses:                     0
% 2.34/0.98  res_num_in_passive:                     0
% 2.34/0.98  res_num_in_active:                      0
% 2.34/0.98  res_num_of_loops:                       100
% 2.34/0.98  res_forward_subset_subsumed:            23
% 2.34/0.98  res_backward_subset_subsumed:           0
% 2.34/0.98  res_forward_subsumed:                   0
% 2.34/0.98  res_backward_subsumed:                  0
% 2.34/0.98  res_forward_subsumption_resolution:     0
% 2.34/0.98  res_backward_subsumption_resolution:    0
% 2.34/0.98  res_clause_to_clause_subsumption:       481
% 2.34/0.98  res_orphan_elimination:                 0
% 2.34/0.98  res_tautology_del:                      58
% 2.34/0.98  res_num_eq_res_simplified:              0
% 2.34/0.98  res_num_sel_changes:                    0
% 2.34/0.98  res_moves_from_active_to_pass:          0
% 2.34/0.98  
% 2.34/0.98  ------ Superposition
% 2.34/0.98  
% 2.34/0.98  sup_time_total:                         0.
% 2.34/0.98  sup_time_generating:                    0.
% 2.34/0.98  sup_time_sim_full:                      0.
% 2.34/0.98  sup_time_sim_immed:                     0.
% 2.34/0.98  
% 2.34/0.98  sup_num_of_clauses:                     49
% 2.34/0.98  sup_num_in_active:                      26
% 2.34/0.98  sup_num_in_passive:                     23
% 2.34/0.98  sup_num_of_loops:                       32
% 2.34/0.98  sup_fw_superposition:                   31
% 2.34/0.98  sup_bw_superposition:                   13
% 2.34/0.98  sup_immediate_simplified:               7
% 2.34/0.98  sup_given_eliminated:                   1
% 2.34/0.98  comparisons_done:                       0
% 2.34/0.98  comparisons_avoided:                    0
% 2.34/0.98  
% 2.34/0.98  ------ Simplifications
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  sim_fw_subset_subsumed:                 3
% 2.34/0.98  sim_bw_subset_subsumed:                 3
% 2.34/0.98  sim_fw_subsumed:                        2
% 2.34/0.98  sim_bw_subsumed:                        1
% 2.34/0.98  sim_fw_subsumption_res:                 0
% 2.34/0.98  sim_bw_subsumption_res:                 0
% 2.34/0.98  sim_tautology_del:                      2
% 2.34/0.98  sim_eq_tautology_del:                   3
% 2.34/0.98  sim_eq_res_simp:                        0
% 2.34/0.98  sim_fw_demodulated:                     1
% 2.34/0.98  sim_bw_demodulated:                     3
% 2.34/0.98  sim_light_normalised:                   1
% 2.34/0.98  sim_joinable_taut:                      0
% 2.34/0.98  sim_joinable_simp:                      0
% 2.34/0.98  sim_ac_normalised:                      0
% 2.34/0.98  sim_smt_subsumption:                    0
% 2.34/0.98  
%------------------------------------------------------------------------------

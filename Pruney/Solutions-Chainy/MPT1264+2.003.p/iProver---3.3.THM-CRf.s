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
% DateTime   : Thu Dec  3 12:14:52 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 432 expanded)
%              Number of clauses        :   72 ( 126 expanded)
%              Number of leaves         :   19 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          :  392 (1972 expanded)
%              Number of equality atoms :  147 ( 468 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
          & v3_pre_topc(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X0,sK3) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK3,X1))
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,sK2))
            & v3_pre_topc(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v1_tops_1(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1))
              & v3_pre_topc(X2,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & v1_tops_1(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))
    & v3_pre_topc(sK3,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & v1_tops_1(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f36,f35,f34])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    v1_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_683,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_361,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_362,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK3)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_678,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_15,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_263,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_15,c_14])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_298,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_263,c_24])).

cnf(c_299,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_744,plain,
    ( k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_678,c_299])).

cnf(c_1008,plain,
    ( r2_hidden(X0,k2_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_744])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_684,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5476,plain,
    ( k4_xboole_0(X0,k2_struct_0(sK1)) = X1
    | r2_hidden(sK0(X0,k2_struct_0(sK1),X1),X1) = iProver_top
    | r2_hidden(sK0(X0,k2_struct_0(sK1),X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1008,c_684])).

cnf(c_6377,plain,
    ( k4_xboole_0(sK3,k2_struct_0(sK1)) = X0
    | r2_hidden(sK0(sK3,k2_struct_0(sK1),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_5476])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_679,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_6470,plain,
    ( k4_xboole_0(sK3,k2_struct_0(sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6377,c_679])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6812,plain,
    ( k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6470,c_12])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6817,plain,
    ( k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))) = sK3 ),
    inference(demodulation,[status(thm)],[c_6812,c_7])).

cnf(c_8,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_352,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_353,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k9_subset_1(X1,X0,sK3)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_731,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k9_subset_1(X1,X0,sK3)
    | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X1) ),
    inference(light_normalisation,[status(thm)],[c_353,c_299])).

cnf(c_732,plain,
    ( k9_subset_1(X0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0) ),
    inference(demodulation,[status(thm)],[c_731,c_12])).

cnf(c_1278,plain,
    ( k9_subset_1(k2_struct_0(sK1),X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(equality_resolution,[status(thm)],[c_732])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_376,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_377,plain,
    ( k9_subset_1(X0,X1,sK3) = k9_subset_1(X0,sK3,X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_720,plain,
    ( k9_subset_1(X0,sK3,X1) = k9_subset_1(X0,X1,sK3)
    | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_377,c_299])).

cnf(c_857,plain,
    ( k9_subset_1(k2_struct_0(sK1),X0,sK3) = k9_subset_1(k2_struct_0(sK1),sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_720])).

cnf(c_1378,plain,
    ( k9_subset_1(k2_struct_0(sK1),sK3,X0) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(demodulation,[status(thm)],[c_1278,c_857])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_385,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_386,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(X1,X0,sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_725,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(X1,X0,sK2)
    | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X1) ),
    inference(light_normalisation,[status(thm)],[c_386,c_299])).

cnf(c_726,plain,
    ( k9_subset_1(X0,X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2))
    | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0) ),
    inference(demodulation,[status(thm)],[c_725,c_12])).

cnf(c_903,plain,
    ( k9_subset_1(k2_struct_0(sK1),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(equality_resolution,[status(thm)],[c_726])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2))
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_278,c_25,c_24,c_21])).

cnf(c_423,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_282])).

cnf(c_424,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_22,negated_conjecture,
    ( v1_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_303,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_304,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_304])).

cnf(c_344,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_346,plain,
    ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_23])).

cnf(c_709,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_424,c_299,c_346])).

cnf(c_1281,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_903,c_709])).

cnf(c_1665,plain,
    ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(k2_struct_0(sK1),sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_1378,c_1281])).

cnf(c_1669,plain,
    ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1)))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_8,c_1665])).

cnf(c_8064,plain,
    ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) = k2_pre_topc(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_6817,c_1669])).

cnf(c_19,negated_conjecture,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_698,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) != k2_pre_topc(sK1,sK3) ),
    inference(light_normalisation,[status(thm)],[c_19,c_299])).

cnf(c_1282,plain,
    ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) != k2_pre_topc(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_903,c_698])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8064,c_1282])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.03  
% 3.60/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.03  
% 3.60/1.03  ------  iProver source info
% 3.60/1.03  
% 3.60/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.03  git: non_committed_changes: false
% 3.60/1.03  git: last_make_outside_of_git: false
% 3.60/1.03  
% 3.60/1.03  ------ 
% 3.60/1.03  
% 3.60/1.03  ------ Input Options
% 3.60/1.03  
% 3.60/1.03  --out_options                           all
% 3.60/1.03  --tptp_safe_out                         true
% 3.60/1.03  --problem_path                          ""
% 3.60/1.03  --include_path                          ""
% 3.60/1.03  --clausifier                            res/vclausify_rel
% 3.60/1.03  --clausifier_options                    --mode clausify
% 3.60/1.03  --stdin                                 false
% 3.60/1.03  --stats_out                             all
% 3.60/1.03  
% 3.60/1.03  ------ General Options
% 3.60/1.03  
% 3.60/1.03  --fof                                   false
% 3.60/1.03  --time_out_real                         305.
% 3.60/1.03  --time_out_virtual                      -1.
% 3.60/1.03  --symbol_type_check                     false
% 3.60/1.03  --clausify_out                          false
% 3.60/1.03  --sig_cnt_out                           false
% 3.60/1.03  --trig_cnt_out                          false
% 3.60/1.03  --trig_cnt_out_tolerance                1.
% 3.60/1.03  --trig_cnt_out_sk_spl                   false
% 3.60/1.03  --abstr_cl_out                          false
% 3.60/1.03  
% 3.60/1.03  ------ Global Options
% 3.60/1.03  
% 3.60/1.03  --schedule                              default
% 3.60/1.03  --add_important_lit                     false
% 3.60/1.03  --prop_solver_per_cl                    1000
% 3.60/1.03  --min_unsat_core                        false
% 3.60/1.03  --soft_assumptions                      false
% 3.60/1.03  --soft_lemma_size                       3
% 3.60/1.03  --prop_impl_unit_size                   0
% 3.60/1.03  --prop_impl_unit                        []
% 3.60/1.03  --share_sel_clauses                     true
% 3.60/1.03  --reset_solvers                         false
% 3.60/1.03  --bc_imp_inh                            [conj_cone]
% 3.60/1.03  --conj_cone_tolerance                   3.
% 3.60/1.03  --extra_neg_conj                        none
% 3.60/1.03  --large_theory_mode                     true
% 3.60/1.03  --prolific_symb_bound                   200
% 3.60/1.03  --lt_threshold                          2000
% 3.60/1.03  --clause_weak_htbl                      true
% 3.60/1.03  --gc_record_bc_elim                     false
% 3.60/1.03  
% 3.60/1.03  ------ Preprocessing Options
% 3.60/1.03  
% 3.60/1.03  --preprocessing_flag                    true
% 3.60/1.03  --time_out_prep_mult                    0.1
% 3.60/1.03  --splitting_mode                        input
% 3.60/1.03  --splitting_grd                         true
% 3.60/1.03  --splitting_cvd                         false
% 3.60/1.03  --splitting_cvd_svl                     false
% 3.60/1.03  --splitting_nvd                         32
% 3.60/1.03  --sub_typing                            true
% 3.60/1.03  --prep_gs_sim                           true
% 3.60/1.03  --prep_unflatten                        true
% 3.60/1.03  --prep_res_sim                          true
% 3.60/1.03  --prep_upred                            true
% 3.60/1.03  --prep_sem_filter                       exhaustive
% 3.60/1.03  --prep_sem_filter_out                   false
% 3.60/1.03  --pred_elim                             true
% 3.60/1.03  --res_sim_input                         true
% 3.60/1.03  --eq_ax_congr_red                       true
% 3.60/1.03  --pure_diseq_elim                       true
% 3.60/1.03  --brand_transform                       false
% 3.60/1.03  --non_eq_to_eq                          false
% 3.60/1.03  --prep_def_merge                        true
% 3.60/1.03  --prep_def_merge_prop_impl              false
% 3.60/1.03  --prep_def_merge_mbd                    true
% 3.60/1.03  --prep_def_merge_tr_red                 false
% 3.60/1.03  --prep_def_merge_tr_cl                  false
% 3.60/1.03  --smt_preprocessing                     true
% 3.60/1.03  --smt_ac_axioms                         fast
% 3.60/1.03  --preprocessed_out                      false
% 3.60/1.03  --preprocessed_stats                    false
% 3.60/1.03  
% 3.60/1.03  ------ Abstraction refinement Options
% 3.60/1.03  
% 3.60/1.03  --abstr_ref                             []
% 3.60/1.03  --abstr_ref_prep                        false
% 3.60/1.03  --abstr_ref_until_sat                   false
% 3.60/1.03  --abstr_ref_sig_restrict                funpre
% 3.60/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.03  --abstr_ref_under                       []
% 3.60/1.03  
% 3.60/1.03  ------ SAT Options
% 3.60/1.03  
% 3.60/1.03  --sat_mode                              false
% 3.60/1.03  --sat_fm_restart_options                ""
% 3.60/1.03  --sat_gr_def                            false
% 3.60/1.03  --sat_epr_types                         true
% 3.60/1.03  --sat_non_cyclic_types                  false
% 3.60/1.03  --sat_finite_models                     false
% 3.60/1.03  --sat_fm_lemmas                         false
% 3.60/1.03  --sat_fm_prep                           false
% 3.60/1.03  --sat_fm_uc_incr                        true
% 3.60/1.03  --sat_out_model                         small
% 3.60/1.03  --sat_out_clauses                       false
% 3.60/1.03  
% 3.60/1.03  ------ QBF Options
% 3.60/1.03  
% 3.60/1.03  --qbf_mode                              false
% 3.60/1.03  --qbf_elim_univ                         false
% 3.60/1.03  --qbf_dom_inst                          none
% 3.60/1.03  --qbf_dom_pre_inst                      false
% 3.60/1.03  --qbf_sk_in                             false
% 3.60/1.03  --qbf_pred_elim                         true
% 3.60/1.03  --qbf_split                             512
% 3.60/1.03  
% 3.60/1.03  ------ BMC1 Options
% 3.60/1.03  
% 3.60/1.03  --bmc1_incremental                      false
% 3.60/1.03  --bmc1_axioms                           reachable_all
% 3.60/1.03  --bmc1_min_bound                        0
% 3.60/1.03  --bmc1_max_bound                        -1
% 3.60/1.03  --bmc1_max_bound_default                -1
% 3.60/1.03  --bmc1_symbol_reachability              true
% 3.60/1.03  --bmc1_property_lemmas                  false
% 3.60/1.03  --bmc1_k_induction                      false
% 3.60/1.03  --bmc1_non_equiv_states                 false
% 3.60/1.03  --bmc1_deadlock                         false
% 3.60/1.03  --bmc1_ucm                              false
% 3.60/1.03  --bmc1_add_unsat_core                   none
% 3.60/1.03  --bmc1_unsat_core_children              false
% 3.60/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.03  --bmc1_out_stat                         full
% 3.60/1.03  --bmc1_ground_init                      false
% 3.60/1.03  --bmc1_pre_inst_next_state              false
% 3.60/1.03  --bmc1_pre_inst_state                   false
% 3.60/1.03  --bmc1_pre_inst_reach_state             false
% 3.60/1.03  --bmc1_out_unsat_core                   false
% 3.60/1.03  --bmc1_aig_witness_out                  false
% 3.60/1.03  --bmc1_verbose                          false
% 3.60/1.03  --bmc1_dump_clauses_tptp                false
% 3.60/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.03  --bmc1_dump_file                        -
% 3.60/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.03  --bmc1_ucm_extend_mode                  1
% 3.60/1.03  --bmc1_ucm_init_mode                    2
% 3.60/1.03  --bmc1_ucm_cone_mode                    none
% 3.60/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.03  --bmc1_ucm_relax_model                  4
% 3.60/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.03  --bmc1_ucm_layered_model                none
% 3.60/1.03  --bmc1_ucm_max_lemma_size               10
% 3.60/1.03  
% 3.60/1.03  ------ AIG Options
% 3.60/1.03  
% 3.60/1.03  --aig_mode                              false
% 3.60/1.03  
% 3.60/1.03  ------ Instantiation Options
% 3.60/1.03  
% 3.60/1.03  --instantiation_flag                    true
% 3.60/1.03  --inst_sos_flag                         false
% 3.60/1.03  --inst_sos_phase                        true
% 3.60/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.03  --inst_lit_sel_side                     num_symb
% 3.60/1.03  --inst_solver_per_active                1400
% 3.60/1.03  --inst_solver_calls_frac                1.
% 3.60/1.03  --inst_passive_queue_type               priority_queues
% 3.60/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.03  --inst_passive_queues_freq              [25;2]
% 3.60/1.03  --inst_dismatching                      true
% 3.60/1.03  --inst_eager_unprocessed_to_passive     true
% 3.60/1.03  --inst_prop_sim_given                   true
% 3.60/1.03  --inst_prop_sim_new                     false
% 3.60/1.03  --inst_subs_new                         false
% 3.60/1.03  --inst_eq_res_simp                      false
% 3.60/1.03  --inst_subs_given                       false
% 3.60/1.03  --inst_orphan_elimination               true
% 3.60/1.03  --inst_learning_loop_flag               true
% 3.60/1.03  --inst_learning_start                   3000
% 3.60/1.03  --inst_learning_factor                  2
% 3.60/1.03  --inst_start_prop_sim_after_learn       3
% 3.60/1.03  --inst_sel_renew                        solver
% 3.60/1.03  --inst_lit_activity_flag                true
% 3.60/1.03  --inst_restr_to_given                   false
% 3.60/1.03  --inst_activity_threshold               500
% 3.60/1.03  --inst_out_proof                        true
% 3.60/1.03  
% 3.60/1.03  ------ Resolution Options
% 3.60/1.03  
% 3.60/1.03  --resolution_flag                       true
% 3.60/1.03  --res_lit_sel                           adaptive
% 3.60/1.03  --res_lit_sel_side                      none
% 3.60/1.03  --res_ordering                          kbo
% 3.60/1.03  --res_to_prop_solver                    active
% 3.60/1.03  --res_prop_simpl_new                    false
% 3.60/1.03  --res_prop_simpl_given                  true
% 3.60/1.03  --res_passive_queue_type                priority_queues
% 3.60/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.03  --res_passive_queues_freq               [15;5]
% 3.60/1.03  --res_forward_subs                      full
% 3.60/1.03  --res_backward_subs                     full
% 3.60/1.03  --res_forward_subs_resolution           true
% 3.60/1.03  --res_backward_subs_resolution          true
% 3.60/1.03  --res_orphan_elimination                true
% 3.60/1.03  --res_time_limit                        2.
% 3.60/1.03  --res_out_proof                         true
% 3.60/1.03  
% 3.60/1.03  ------ Superposition Options
% 3.60/1.03  
% 3.60/1.03  --superposition_flag                    true
% 3.60/1.03  --sup_passive_queue_type                priority_queues
% 3.60/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.03  --demod_completeness_check              fast
% 3.60/1.03  --demod_use_ground                      true
% 3.60/1.03  --sup_to_prop_solver                    passive
% 3.60/1.03  --sup_prop_simpl_new                    true
% 3.60/1.03  --sup_prop_simpl_given                  true
% 3.60/1.03  --sup_fun_splitting                     false
% 3.60/1.03  --sup_smt_interval                      50000
% 3.60/1.03  
% 3.60/1.03  ------ Superposition Simplification Setup
% 3.60/1.03  
% 3.60/1.03  --sup_indices_passive                   []
% 3.60/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.03  --sup_full_bw                           [BwDemod]
% 3.60/1.03  --sup_immed_triv                        [TrivRules]
% 3.60/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.03  --sup_immed_bw_main                     []
% 3.60/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.03  
% 3.60/1.03  ------ Combination Options
% 3.60/1.03  
% 3.60/1.03  --comb_res_mult                         3
% 3.60/1.03  --comb_sup_mult                         2
% 3.60/1.03  --comb_inst_mult                        10
% 3.60/1.03  
% 3.60/1.03  ------ Debug Options
% 3.60/1.03  
% 3.60/1.03  --dbg_backtrace                         false
% 3.60/1.03  --dbg_dump_prop_clauses                 false
% 3.60/1.03  --dbg_dump_prop_clauses_file            -
% 3.60/1.03  --dbg_out_stat                          false
% 3.60/1.03  ------ Parsing...
% 3.60/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.03  
% 3.60/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.60/1.03  
% 3.60/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.03  
% 3.60/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.03  ------ Proving...
% 3.60/1.03  ------ Problem Properties 
% 3.60/1.03  
% 3.60/1.03  
% 3.60/1.03  clauses                                 21
% 3.60/1.03  conjectures                             1
% 3.60/1.03  EPR                                     1
% 3.60/1.03  Horn                                    17
% 3.60/1.03  unary                                   9
% 3.60/1.03  binary                                  6
% 3.60/1.03  lits                                    40
% 3.60/1.03  lits eq                                 21
% 3.60/1.03  fd_pure                                 0
% 3.60/1.03  fd_pseudo                               0
% 3.60/1.03  fd_cond                                 0
% 3.60/1.03  fd_pseudo_cond                          3
% 3.60/1.03  AC symbols                              0
% 3.60/1.03  
% 3.60/1.03  ------ Schedule dynamic 5 is on 
% 3.60/1.03  
% 3.60/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/1.03  
% 3.60/1.03  
% 3.60/1.03  ------ 
% 3.60/1.03  Current options:
% 3.60/1.03  ------ 
% 3.60/1.03  
% 3.60/1.03  ------ Input Options
% 3.60/1.03  
% 3.60/1.03  --out_options                           all
% 3.60/1.03  --tptp_safe_out                         true
% 3.60/1.03  --problem_path                          ""
% 3.60/1.03  --include_path                          ""
% 3.60/1.03  --clausifier                            res/vclausify_rel
% 3.60/1.03  --clausifier_options                    --mode clausify
% 3.60/1.03  --stdin                                 false
% 3.60/1.03  --stats_out                             all
% 3.60/1.03  
% 3.60/1.03  ------ General Options
% 3.60/1.03  
% 3.60/1.03  --fof                                   false
% 3.60/1.03  --time_out_real                         305.
% 3.60/1.03  --time_out_virtual                      -1.
% 3.60/1.03  --symbol_type_check                     false
% 3.60/1.03  --clausify_out                          false
% 3.60/1.03  --sig_cnt_out                           false
% 3.60/1.03  --trig_cnt_out                          false
% 3.60/1.03  --trig_cnt_out_tolerance                1.
% 3.60/1.03  --trig_cnt_out_sk_spl                   false
% 3.60/1.03  --abstr_cl_out                          false
% 3.60/1.03  
% 3.60/1.03  ------ Global Options
% 3.60/1.03  
% 3.60/1.03  --schedule                              default
% 3.60/1.03  --add_important_lit                     false
% 3.60/1.03  --prop_solver_per_cl                    1000
% 3.60/1.03  --min_unsat_core                        false
% 3.60/1.03  --soft_assumptions                      false
% 3.60/1.03  --soft_lemma_size                       3
% 3.60/1.03  --prop_impl_unit_size                   0
% 3.60/1.03  --prop_impl_unit                        []
% 3.60/1.03  --share_sel_clauses                     true
% 3.60/1.03  --reset_solvers                         false
% 3.60/1.03  --bc_imp_inh                            [conj_cone]
% 3.60/1.03  --conj_cone_tolerance                   3.
% 3.60/1.03  --extra_neg_conj                        none
% 3.60/1.03  --large_theory_mode                     true
% 3.60/1.03  --prolific_symb_bound                   200
% 3.60/1.03  --lt_threshold                          2000
% 3.60/1.03  --clause_weak_htbl                      true
% 3.60/1.03  --gc_record_bc_elim                     false
% 3.60/1.03  
% 3.60/1.03  ------ Preprocessing Options
% 3.60/1.03  
% 3.60/1.03  --preprocessing_flag                    true
% 3.60/1.03  --time_out_prep_mult                    0.1
% 3.60/1.03  --splitting_mode                        input
% 3.60/1.03  --splitting_grd                         true
% 3.60/1.03  --splitting_cvd                         false
% 3.60/1.03  --splitting_cvd_svl                     false
% 3.60/1.03  --splitting_nvd                         32
% 3.60/1.03  --sub_typing                            true
% 3.60/1.03  --prep_gs_sim                           true
% 3.60/1.03  --prep_unflatten                        true
% 3.60/1.03  --prep_res_sim                          true
% 3.60/1.03  --prep_upred                            true
% 3.60/1.03  --prep_sem_filter                       exhaustive
% 3.60/1.03  --prep_sem_filter_out                   false
% 3.60/1.03  --pred_elim                             true
% 3.60/1.03  --res_sim_input                         true
% 3.60/1.03  --eq_ax_congr_red                       true
% 3.60/1.03  --pure_diseq_elim                       true
% 3.60/1.03  --brand_transform                       false
% 3.60/1.03  --non_eq_to_eq                          false
% 3.60/1.03  --prep_def_merge                        true
% 3.60/1.03  --prep_def_merge_prop_impl              false
% 3.60/1.03  --prep_def_merge_mbd                    true
% 3.60/1.03  --prep_def_merge_tr_red                 false
% 3.60/1.03  --prep_def_merge_tr_cl                  false
% 3.60/1.03  --smt_preprocessing                     true
% 3.60/1.03  --smt_ac_axioms                         fast
% 3.60/1.03  --preprocessed_out                      false
% 3.60/1.03  --preprocessed_stats                    false
% 3.60/1.03  
% 3.60/1.03  ------ Abstraction refinement Options
% 3.60/1.03  
% 3.60/1.03  --abstr_ref                             []
% 3.60/1.03  --abstr_ref_prep                        false
% 3.60/1.03  --abstr_ref_until_sat                   false
% 3.60/1.03  --abstr_ref_sig_restrict                funpre
% 3.60/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.03  --abstr_ref_under                       []
% 3.60/1.03  
% 3.60/1.03  ------ SAT Options
% 3.60/1.03  
% 3.60/1.03  --sat_mode                              false
% 3.60/1.03  --sat_fm_restart_options                ""
% 3.60/1.03  --sat_gr_def                            false
% 3.60/1.03  --sat_epr_types                         true
% 3.60/1.03  --sat_non_cyclic_types                  false
% 3.60/1.03  --sat_finite_models                     false
% 3.60/1.03  --sat_fm_lemmas                         false
% 3.60/1.03  --sat_fm_prep                           false
% 3.60/1.03  --sat_fm_uc_incr                        true
% 3.60/1.03  --sat_out_model                         small
% 3.60/1.03  --sat_out_clauses                       false
% 3.60/1.03  
% 3.60/1.03  ------ QBF Options
% 3.60/1.03  
% 3.60/1.03  --qbf_mode                              false
% 3.60/1.03  --qbf_elim_univ                         false
% 3.60/1.03  --qbf_dom_inst                          none
% 3.60/1.03  --qbf_dom_pre_inst                      false
% 3.60/1.03  --qbf_sk_in                             false
% 3.60/1.03  --qbf_pred_elim                         true
% 3.60/1.03  --qbf_split                             512
% 3.60/1.03  
% 3.60/1.03  ------ BMC1 Options
% 3.60/1.03  
% 3.60/1.03  --bmc1_incremental                      false
% 3.60/1.03  --bmc1_axioms                           reachable_all
% 3.60/1.03  --bmc1_min_bound                        0
% 3.60/1.03  --bmc1_max_bound                        -1
% 3.60/1.03  --bmc1_max_bound_default                -1
% 3.60/1.03  --bmc1_symbol_reachability              true
% 3.60/1.03  --bmc1_property_lemmas                  false
% 3.60/1.03  --bmc1_k_induction                      false
% 3.60/1.03  --bmc1_non_equiv_states                 false
% 3.60/1.03  --bmc1_deadlock                         false
% 3.60/1.03  --bmc1_ucm                              false
% 3.60/1.03  --bmc1_add_unsat_core                   none
% 3.60/1.03  --bmc1_unsat_core_children              false
% 3.60/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.03  --bmc1_out_stat                         full
% 3.60/1.03  --bmc1_ground_init                      false
% 3.60/1.03  --bmc1_pre_inst_next_state              false
% 3.60/1.03  --bmc1_pre_inst_state                   false
% 3.60/1.03  --bmc1_pre_inst_reach_state             false
% 3.60/1.03  --bmc1_out_unsat_core                   false
% 3.60/1.03  --bmc1_aig_witness_out                  false
% 3.60/1.03  --bmc1_verbose                          false
% 3.60/1.03  --bmc1_dump_clauses_tptp                false
% 3.60/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.03  --bmc1_dump_file                        -
% 3.60/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.03  --bmc1_ucm_extend_mode                  1
% 3.60/1.03  --bmc1_ucm_init_mode                    2
% 3.60/1.03  --bmc1_ucm_cone_mode                    none
% 3.60/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.03  --bmc1_ucm_relax_model                  4
% 3.60/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.03  --bmc1_ucm_layered_model                none
% 3.60/1.03  --bmc1_ucm_max_lemma_size               10
% 3.60/1.03  
% 3.60/1.03  ------ AIG Options
% 3.60/1.03  
% 3.60/1.03  --aig_mode                              false
% 3.60/1.03  
% 3.60/1.03  ------ Instantiation Options
% 3.60/1.03  
% 3.60/1.03  --instantiation_flag                    true
% 3.60/1.03  --inst_sos_flag                         false
% 3.60/1.03  --inst_sos_phase                        true
% 3.60/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.03  --inst_lit_sel_side                     none
% 3.60/1.03  --inst_solver_per_active                1400
% 3.60/1.03  --inst_solver_calls_frac                1.
% 3.60/1.03  --inst_passive_queue_type               priority_queues
% 3.60/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.03  --inst_passive_queues_freq              [25;2]
% 3.60/1.03  --inst_dismatching                      true
% 3.60/1.03  --inst_eager_unprocessed_to_passive     true
% 3.60/1.03  --inst_prop_sim_given                   true
% 3.60/1.03  --inst_prop_sim_new                     false
% 3.60/1.03  --inst_subs_new                         false
% 3.60/1.03  --inst_eq_res_simp                      false
% 3.60/1.03  --inst_subs_given                       false
% 3.60/1.03  --inst_orphan_elimination               true
% 3.60/1.03  --inst_learning_loop_flag               true
% 3.60/1.03  --inst_learning_start                   3000
% 3.60/1.03  --inst_learning_factor                  2
% 3.60/1.03  --inst_start_prop_sim_after_learn       3
% 3.60/1.03  --inst_sel_renew                        solver
% 3.60/1.03  --inst_lit_activity_flag                true
% 3.60/1.03  --inst_restr_to_given                   false
% 3.60/1.03  --inst_activity_threshold               500
% 3.60/1.03  --inst_out_proof                        true
% 3.60/1.03  
% 3.60/1.03  ------ Resolution Options
% 3.60/1.03  
% 3.60/1.03  --resolution_flag                       false
% 3.60/1.03  --res_lit_sel                           adaptive
% 3.60/1.03  --res_lit_sel_side                      none
% 3.60/1.03  --res_ordering                          kbo
% 3.60/1.03  --res_to_prop_solver                    active
% 3.60/1.03  --res_prop_simpl_new                    false
% 3.60/1.03  --res_prop_simpl_given                  true
% 3.60/1.03  --res_passive_queue_type                priority_queues
% 3.60/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.03  --res_passive_queues_freq               [15;5]
% 3.60/1.03  --res_forward_subs                      full
% 3.60/1.03  --res_backward_subs                     full
% 3.60/1.03  --res_forward_subs_resolution           true
% 3.60/1.03  --res_backward_subs_resolution          true
% 3.60/1.03  --res_orphan_elimination                true
% 3.60/1.03  --res_time_limit                        2.
% 3.60/1.03  --res_out_proof                         true
% 3.60/1.03  
% 3.60/1.03  ------ Superposition Options
% 3.60/1.03  
% 3.60/1.03  --superposition_flag                    true
% 3.60/1.03  --sup_passive_queue_type                priority_queues
% 3.60/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.03  --demod_completeness_check              fast
% 3.60/1.03  --demod_use_ground                      true
% 3.60/1.03  --sup_to_prop_solver                    passive
% 3.60/1.03  --sup_prop_simpl_new                    true
% 3.60/1.03  --sup_prop_simpl_given                  true
% 3.60/1.03  --sup_fun_splitting                     false
% 3.60/1.03  --sup_smt_interval                      50000
% 3.60/1.03  
% 3.60/1.03  ------ Superposition Simplification Setup
% 3.60/1.03  
% 3.60/1.03  --sup_indices_passive                   []
% 3.60/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.03  --sup_full_bw                           [BwDemod]
% 3.60/1.03  --sup_immed_triv                        [TrivRules]
% 3.60/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.03  --sup_immed_bw_main                     []
% 3.60/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.03  
% 3.60/1.03  ------ Combination Options
% 3.60/1.03  
% 3.60/1.03  --comb_res_mult                         3
% 3.60/1.03  --comb_sup_mult                         2
% 3.60/1.03  --comb_inst_mult                        10
% 3.60/1.03  
% 3.60/1.03  ------ Debug Options
% 3.60/1.03  
% 3.60/1.03  --dbg_backtrace                         false
% 3.60/1.03  --dbg_dump_prop_clauses                 false
% 3.60/1.03  --dbg_dump_prop_clauses_file            -
% 3.60/1.03  --dbg_out_stat                          false
% 3.60/1.03  
% 3.60/1.03  
% 3.60/1.03  
% 3.60/1.03  
% 3.60/1.03  ------ Proving...
% 3.60/1.03  
% 3.60/1.03  
% 3.60/1.03  % SZS status Theorem for theBenchmark.p
% 3.60/1.03  
% 3.60/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.03  
% 3.60/1.03  fof(f1,axiom,(
% 3.60/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f28,plain,(
% 3.60/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.03    inference(nnf_transformation,[],[f1])).
% 3.60/1.03  
% 3.60/1.03  fof(f29,plain,(
% 3.60/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.03    inference(flattening,[],[f28])).
% 3.60/1.03  
% 3.60/1.03  fof(f30,plain,(
% 3.60/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.03    inference(rectify,[],[f29])).
% 3.60/1.03  
% 3.60/1.03  fof(f31,plain,(
% 3.60/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.60/1.03    introduced(choice_axiom,[])).
% 3.60/1.03  
% 3.60/1.03  fof(f32,plain,(
% 3.60/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.60/1.03  
% 3.60/1.03  fof(f41,plain,(
% 3.60/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f32])).
% 3.60/1.03  
% 3.60/1.03  fof(f7,axiom,(
% 3.60/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f18,plain,(
% 3.60/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.60/1.03    inference(ennf_transformation,[],[f7])).
% 3.60/1.03  
% 3.60/1.03  fof(f49,plain,(
% 3.60/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.60/1.03    inference(cnf_transformation,[],[f18])).
% 3.60/1.03  
% 3.60/1.03  fof(f15,conjecture,(
% 3.60/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f16,negated_conjecture,(
% 3.60/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 3.60/1.03    inference(negated_conjecture,[],[f15])).
% 3.60/1.03  
% 3.60/1.03  fof(f26,plain,(
% 3.60/1.03    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.60/1.03    inference(ennf_transformation,[],[f16])).
% 3.60/1.03  
% 3.60/1.03  fof(f27,plain,(
% 3.60/1.03    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.60/1.03    inference(flattening,[],[f26])).
% 3.60/1.03  
% 3.60/1.03  fof(f36,plain,(
% 3.60/1.03    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_pre_topc(X0,sK3) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK3,X1)) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.60/1.03    introduced(choice_axiom,[])).
% 3.60/1.03  
% 3.60/1.03  fof(f35,plain,(
% 3.60/1.03    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,sK2)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.60/1.03    introduced(choice_axiom,[])).
% 3.60/1.03  
% 3.60/1.03  fof(f34,plain,(
% 3.60/1.03    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1)) & v3_pre_topc(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.60/1.03    introduced(choice_axiom,[])).
% 3.60/1.03  
% 3.60/1.03  fof(f37,plain,(
% 3.60/1.03    ((k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) & v3_pre_topc(sK3,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 3.60/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f36,f35,f34])).
% 3.60/1.03  
% 3.60/1.03  fof(f62,plain,(
% 3.60/1.03    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.60/1.03    inference(cnf_transformation,[],[f37])).
% 3.60/1.03  
% 3.60/1.03  fof(f12,axiom,(
% 3.60/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f22,plain,(
% 3.60/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.60/1.03    inference(ennf_transformation,[],[f12])).
% 3.60/1.03  
% 3.60/1.03  fof(f54,plain,(
% 3.60/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f22])).
% 3.60/1.03  
% 3.60/1.03  fof(f11,axiom,(
% 3.60/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f21,plain,(
% 3.60/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.60/1.03    inference(ennf_transformation,[],[f11])).
% 3.60/1.03  
% 3.60/1.03  fof(f53,plain,(
% 3.60/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f21])).
% 3.60/1.03  
% 3.60/1.03  fof(f59,plain,(
% 3.60/1.03    l1_pre_topc(sK1)),
% 3.60/1.03    inference(cnf_transformation,[],[f37])).
% 3.60/1.03  
% 3.60/1.03  fof(f42,plain,(
% 3.60/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f32])).
% 3.60/1.03  
% 3.60/1.03  fof(f2,axiom,(
% 3.60/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f44,plain,(
% 3.60/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f2])).
% 3.60/1.03  
% 3.60/1.03  fof(f10,axiom,(
% 3.60/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f20,plain,(
% 3.60/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.60/1.03    inference(ennf_transformation,[],[f10])).
% 3.60/1.03  
% 3.60/1.03  fof(f52,plain,(
% 3.60/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f20])).
% 3.60/1.03  
% 3.60/1.03  fof(f9,axiom,(
% 3.60/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f51,plain,(
% 3.60/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.60/1.03    inference(cnf_transformation,[],[f9])).
% 3.60/1.03  
% 3.60/1.03  fof(f4,axiom,(
% 3.60/1.03    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f46,plain,(
% 3.60/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f4])).
% 3.60/1.03  
% 3.60/1.03  fof(f66,plain,(
% 3.60/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.60/1.03    inference(definition_unfolding,[],[f51,f46])).
% 3.60/1.03  
% 3.60/1.03  fof(f3,axiom,(
% 3.60/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f45,plain,(
% 3.60/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.60/1.03    inference(cnf_transformation,[],[f3])).
% 3.60/1.03  
% 3.60/1.03  fof(f5,axiom,(
% 3.60/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f47,plain,(
% 3.60/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f5])).
% 3.60/1.03  
% 3.60/1.03  fof(f8,axiom,(
% 3.60/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f19,plain,(
% 3.60/1.03    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.60/1.03    inference(ennf_transformation,[],[f8])).
% 3.60/1.03  
% 3.60/1.03  fof(f50,plain,(
% 3.60/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.60/1.03    inference(cnf_transformation,[],[f19])).
% 3.60/1.03  
% 3.60/1.03  fof(f65,plain,(
% 3.60/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.60/1.03    inference(definition_unfolding,[],[f50,f46])).
% 3.60/1.03  
% 3.60/1.03  fof(f6,axiom,(
% 3.60/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f17,plain,(
% 3.60/1.03    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.60/1.03    inference(ennf_transformation,[],[f6])).
% 3.60/1.03  
% 3.60/1.03  fof(f48,plain,(
% 3.60/1.03    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.60/1.03    inference(cnf_transformation,[],[f17])).
% 3.60/1.03  
% 3.60/1.03  fof(f60,plain,(
% 3.60/1.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.60/1.03    inference(cnf_transformation,[],[f37])).
% 3.60/1.03  
% 3.60/1.03  fof(f14,axiom,(
% 3.60/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))))))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f24,plain,(
% 3.60/1.03    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.60/1.03    inference(ennf_transformation,[],[f14])).
% 3.60/1.03  
% 3.60/1.03  fof(f25,plain,(
% 3.60/1.03    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.60/1.03    inference(flattening,[],[f24])).
% 3.60/1.03  
% 3.60/1.03  fof(f57,plain,(
% 3.60/1.03    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f25])).
% 3.60/1.03  
% 3.60/1.03  fof(f63,plain,(
% 3.60/1.03    v3_pre_topc(sK3,sK1)),
% 3.60/1.03    inference(cnf_transformation,[],[f37])).
% 3.60/1.03  
% 3.60/1.03  fof(f58,plain,(
% 3.60/1.03    v2_pre_topc(sK1)),
% 3.60/1.03    inference(cnf_transformation,[],[f37])).
% 3.60/1.03  
% 3.60/1.03  fof(f61,plain,(
% 3.60/1.03    v1_tops_1(sK2,sK1)),
% 3.60/1.03    inference(cnf_transformation,[],[f37])).
% 3.60/1.03  
% 3.60/1.03  fof(f13,axiom,(
% 3.60/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.60/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.03  
% 3.60/1.03  fof(f23,plain,(
% 3.60/1.03    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.03    inference(ennf_transformation,[],[f13])).
% 3.60/1.03  
% 3.60/1.03  fof(f33,plain,(
% 3.60/1.03    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.03    inference(nnf_transformation,[],[f23])).
% 3.60/1.03  
% 3.60/1.03  fof(f55,plain,(
% 3.60/1.03    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.03    inference(cnf_transformation,[],[f33])).
% 3.60/1.03  
% 3.60/1.03  fof(f64,plain,(
% 3.60/1.03    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))),
% 3.60/1.03    inference(cnf_transformation,[],[f37])).
% 3.60/1.03  
% 3.60/1.03  cnf(c_2,plain,
% 3.60/1.03      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.60/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.60/1.03      | k4_xboole_0(X0,X1) = X2 ),
% 3.60/1.03      inference(cnf_transformation,[],[f41]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_683,plain,
% 3.60/1.03      ( k4_xboole_0(X0,X1) = X2
% 3.60/1.03      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.60/1.03      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.60/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_10,plain,
% 3.60/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.60/1.03      | ~ r2_hidden(X2,X0)
% 3.60/1.03      | r2_hidden(X2,X1) ),
% 3.60/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_21,negated_conjecture,
% 3.60/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.60/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_361,plain,
% 3.60/1.03      ( ~ r2_hidden(X0,X1)
% 3.60/1.03      | r2_hidden(X0,X2)
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X2)
% 3.60/1.03      | sK3 != X1 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_362,plain,
% 3.60/1.03      ( r2_hidden(X0,X1)
% 3.60/1.03      | ~ r2_hidden(X0,sK3)
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_361]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_678,plain,
% 3.60/1.03      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
% 3.60/1.03      | r2_hidden(X1,X0) = iProver_top
% 3.60/1.03      | r2_hidden(X1,sK3) != iProver_top ),
% 3.60/1.03      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_15,plain,
% 3.60/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.60/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_14,plain,
% 3.60/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.60/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_263,plain,
% 3.60/1.03      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.60/1.03      inference(resolution,[status(thm)],[c_15,c_14]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_24,negated_conjecture,
% 3.60/1.03      ( l1_pre_topc(sK1) ),
% 3.60/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_298,plain,
% 3.60/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_263,c_24]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_299,plain,
% 3.60/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_298]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_744,plain,
% 3.60/1.03      ( k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0)
% 3.60/1.03      | r2_hidden(X1,X0) = iProver_top
% 3.60/1.03      | r2_hidden(X1,sK3) != iProver_top ),
% 3.60/1.03      inference(light_normalisation,[status(thm)],[c_678,c_299]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_1008,plain,
% 3.60/1.03      ( r2_hidden(X0,k2_struct_0(sK1)) = iProver_top
% 3.60/1.03      | r2_hidden(X0,sK3) != iProver_top ),
% 3.60/1.03      inference(equality_resolution,[status(thm)],[c_744]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_1,plain,
% 3.60/1.03      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.60/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.60/1.03      | k4_xboole_0(X0,X1) = X2 ),
% 3.60/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_684,plain,
% 3.60/1.03      ( k4_xboole_0(X0,X1) = X2
% 3.60/1.03      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 3.60/1.03      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.60/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_5476,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k2_struct_0(sK1)) = X1
% 3.60/1.03      | r2_hidden(sK0(X0,k2_struct_0(sK1),X1),X1) = iProver_top
% 3.60/1.03      | r2_hidden(sK0(X0,k2_struct_0(sK1),X1),sK3) != iProver_top ),
% 3.60/1.03      inference(superposition,[status(thm)],[c_1008,c_684]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_6377,plain,
% 3.60/1.03      ( k4_xboole_0(sK3,k2_struct_0(sK1)) = X0
% 3.60/1.03      | r2_hidden(sK0(sK3,k2_struct_0(sK1),X0),X0) = iProver_top ),
% 3.60/1.03      inference(superposition,[status(thm)],[c_683,c_5476]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_6,plain,
% 3.60/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 3.60/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_13,plain,
% 3.60/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.60/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_252,plain,
% 3.60/1.03      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_253,plain,
% 3.60/1.03      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_252]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_679,plain,
% 3.60/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.60/1.03      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_6470,plain,
% 3.60/1.03      ( k4_xboole_0(sK3,k2_struct_0(sK1)) = k1_xboole_0 ),
% 3.60/1.03      inference(superposition,[status(thm)],[c_6377,c_679]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_12,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.60/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_6812,plain,
% 3.60/1.03      ( k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))) = k4_xboole_0(sK3,k1_xboole_0) ),
% 3.60/1.03      inference(superposition,[status(thm)],[c_6470,c_12]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_7,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.60/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_6817,plain,
% 3.60/1.03      ( k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))) = sK3 ),
% 3.60/1.03      inference(demodulation,[status(thm)],[c_6812,c_7]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_8,plain,
% 3.60/1.03      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.60/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_11,plain,
% 3.60/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.60/1.03      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.60/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_352,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X2)
% 3.60/1.03      | sK3 != X1 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_353,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k9_subset_1(X1,X0,sK3)
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_352]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_731,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k9_subset_1(X1,X0,sK3)
% 3.60/1.03      | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X1) ),
% 3.60/1.03      inference(light_normalisation,[status(thm)],[c_353,c_299]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_732,plain,
% 3.60/1.03      ( k9_subset_1(X0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
% 3.60/1.03      | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0) ),
% 3.60/1.03      inference(demodulation,[status(thm)],[c_731,c_12]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_1278,plain,
% 3.60/1.03      ( k9_subset_1(k2_struct_0(sK1),X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
% 3.60/1.03      inference(equality_resolution,[status(thm)],[c_732]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_9,plain,
% 3.60/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.60/1.03      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.60/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_376,plain,
% 3.60/1.03      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
% 3.60/1.03      | sK3 != X2 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_377,plain,
% 3.60/1.03      ( k9_subset_1(X0,X1,sK3) = k9_subset_1(X0,sK3,X1)
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_376]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_720,plain,
% 3.60/1.03      ( k9_subset_1(X0,sK3,X1) = k9_subset_1(X0,X1,sK3)
% 3.60/1.03      | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0) ),
% 3.60/1.03      inference(light_normalisation,[status(thm)],[c_377,c_299]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_857,plain,
% 3.60/1.03      ( k9_subset_1(k2_struct_0(sK1),X0,sK3) = k9_subset_1(k2_struct_0(sK1),sK3,X0) ),
% 3.60/1.03      inference(equality_resolution,[status(thm)],[c_720]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_1378,plain,
% 3.60/1.03      ( k9_subset_1(k2_struct_0(sK1),sK3,X0) = k1_setfam_1(k2_tarski(X0,sK3)) ),
% 3.60/1.03      inference(demodulation,[status(thm)],[c_1278,c_857]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_23,negated_conjecture,
% 3.60/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.60/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_385,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X2)
% 3.60/1.03      | sK2 != X1 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_386,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(X1,X0,sK2)
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_385]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_725,plain,
% 3.60/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(X1,X0,sK2)
% 3.60/1.03      | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X1) ),
% 3.60/1.03      inference(light_normalisation,[status(thm)],[c_386,c_299]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_726,plain,
% 3.60/1.03      ( k9_subset_1(X0,X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2))
% 3.60/1.03      | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0) ),
% 3.60/1.03      inference(demodulation,[status(thm)],[c_725,c_12]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_903,plain,
% 3.60/1.03      ( k9_subset_1(k2_struct_0(sK1),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 3.60/1.03      inference(equality_resolution,[status(thm)],[c_726]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_18,plain,
% 3.60/1.03      ( ~ v3_pre_topc(X0,X1)
% 3.60/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.03      | ~ v2_pre_topc(X1)
% 3.60/1.03      | ~ l1_pre_topc(X1)
% 3.60/1.03      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) ),
% 3.60/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_20,negated_conjecture,
% 3.60/1.03      ( v3_pre_topc(sK3,sK1) ),
% 3.60/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_277,plain,
% 3.60/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.03      | ~ v2_pre_topc(X1)
% 3.60/1.03      | ~ l1_pre_topc(X1)
% 3.60/1.03      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2))
% 3.60/1.03      | sK3 != X0
% 3.60/1.03      | sK1 != X1 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_278,plain,
% 3.60/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.60/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.60/1.03      | ~ v2_pre_topc(sK1)
% 3.60/1.03      | ~ l1_pre_topc(sK1)
% 3.60/1.03      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_277]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_25,negated_conjecture,
% 3.60/1.03      ( v2_pre_topc(sK1) ),
% 3.60/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_282,plain,
% 3.60/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.60/1.03      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
% 3.60/1.03      inference(global_propositional_subsumption,
% 3.60/1.03                [status(thm)],
% 3.60/1.03                [c_278,c_25,c_24,c_21]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_423,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0))
% 3.60/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 3.60/1.03      | sK2 != X0 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_282]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_424,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_423]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_22,negated_conjecture,
% 3.60/1.03      ( v1_tops_1(sK2,sK1) ),
% 3.60/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_17,plain,
% 3.60/1.03      ( ~ v1_tops_1(X0,X1)
% 3.60/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.03      | ~ l1_pre_topc(X1)
% 3.60/1.03      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.60/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_303,plain,
% 3.60/1.03      ( ~ v1_tops_1(X0,X1)
% 3.60/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.03      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 3.60/1.03      | sK1 != X1 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_304,plain,
% 3.60/1.03      ( ~ v1_tops_1(X0,sK1)
% 3.60/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.60/1.03      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_303]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_343,plain,
% 3.60/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.60/1.03      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
% 3.60/1.03      | sK2 != X0
% 3.60/1.03      | sK1 != sK1 ),
% 3.60/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_304]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_344,plain,
% 3.60/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.60/1.03      | k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
% 3.60/1.03      inference(unflattening,[status(thm)],[c_343]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_346,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
% 3.60/1.03      inference(global_propositional_subsumption,
% 3.60/1.03                [status(thm)],
% 3.60/1.03                [c_344,c_23]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_709,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) ),
% 3.60/1.03      inference(light_normalisation,[status(thm)],[c_424,c_299,c_346]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_1281,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) ),
% 3.60/1.03      inference(demodulation,[status(thm)],[c_903,c_709]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_1665,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(k2_struct_0(sK1),sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) ),
% 3.60/1.03      inference(demodulation,[status(thm)],[c_1378,c_1281]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_1669,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1)))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) ),
% 3.60/1.03      inference(superposition,[status(thm)],[c_8,c_1665]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_8064,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) = k2_pre_topc(sK1,sK3) ),
% 3.60/1.03      inference(demodulation,[status(thm)],[c_6817,c_1669]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_19,negated_conjecture,
% 3.60/1.03      ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
% 3.60/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_698,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) != k2_pre_topc(sK1,sK3) ),
% 3.60/1.03      inference(light_normalisation,[status(thm)],[c_19,c_299]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(c_1282,plain,
% 3.60/1.03      ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) != k2_pre_topc(sK1,sK3) ),
% 3.60/1.03      inference(demodulation,[status(thm)],[c_903,c_698]) ).
% 3.60/1.03  
% 3.60/1.03  cnf(contradiction,plain,
% 3.60/1.03      ( $false ),
% 3.60/1.03      inference(minisat,[status(thm)],[c_8064,c_1282]) ).
% 3.60/1.03  
% 3.60/1.03  
% 3.60/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.03  
% 3.60/1.03  ------                               Statistics
% 3.60/1.03  
% 3.60/1.03  ------ General
% 3.60/1.03  
% 3.60/1.03  abstr_ref_over_cycles:                  0
% 3.60/1.03  abstr_ref_under_cycles:                 0
% 3.60/1.03  gc_basic_clause_elim:                   0
% 3.60/1.03  forced_gc_time:                         0
% 3.60/1.03  parsing_time:                           0.013
% 3.60/1.03  unif_index_cands_time:                  0.
% 3.60/1.03  unif_index_add_time:                    0.
% 3.60/1.03  orderings_time:                         0.
% 3.60/1.03  out_proof_time:                         0.009
% 3.60/1.03  total_time:                             0.292
% 3.60/1.03  num_of_symbols:                         52
% 3.60/1.03  num_of_terms:                           9904
% 3.60/1.03  
% 3.60/1.03  ------ Preprocessing
% 3.60/1.03  
% 3.60/1.03  num_of_splits:                          0
% 3.60/1.03  num_of_split_atoms:                     0
% 3.60/1.03  num_of_reused_defs:                     0
% 3.60/1.03  num_eq_ax_congr_red:                    21
% 3.60/1.03  num_of_sem_filtered_clauses:            1
% 3.60/1.03  num_of_subtypes:                        0
% 3.60/1.03  monotx_restored_types:                  0
% 3.60/1.03  sat_num_of_epr_types:                   0
% 3.60/1.03  sat_num_of_non_cyclic_types:            0
% 3.60/1.03  sat_guarded_non_collapsed_types:        0
% 3.60/1.03  num_pure_diseq_elim:                    0
% 3.60/1.03  simp_replaced_by:                       0
% 3.60/1.03  res_preprocessed:                       110
% 3.60/1.03  prep_upred:                             0
% 3.60/1.03  prep_unflattend:                        16
% 3.60/1.03  smt_new_axioms:                         0
% 3.60/1.03  pred_elim_cands:                        1
% 3.60/1.03  pred_elim:                              7
% 3.60/1.03  pred_elim_cl:                           5
% 3.60/1.03  pred_elim_cycles:                       9
% 3.60/1.03  merged_defs:                            0
% 3.60/1.03  merged_defs_ncl:                        0
% 3.60/1.03  bin_hyper_res:                          0
% 3.60/1.03  prep_cycles:                            4
% 3.60/1.03  pred_elim_time:                         0.006
% 3.60/1.03  splitting_time:                         0.
% 3.60/1.03  sem_filter_time:                        0.
% 3.60/1.03  monotx_time:                            0.001
% 3.60/1.03  subtype_inf_time:                       0.
% 3.60/1.03  
% 3.60/1.03  ------ Problem properties
% 3.60/1.03  
% 3.60/1.03  clauses:                                21
% 3.60/1.03  conjectures:                            1
% 3.60/1.03  epr:                                    1
% 3.60/1.03  horn:                                   17
% 3.60/1.03  ground:                                 5
% 3.60/1.03  unary:                                  9
% 3.60/1.03  binary:                                 6
% 3.60/1.03  lits:                                   40
% 3.60/1.03  lits_eq:                                21
% 3.60/1.03  fd_pure:                                0
% 3.60/1.03  fd_pseudo:                              0
% 3.60/1.03  fd_cond:                                0
% 3.60/1.03  fd_pseudo_cond:                         3
% 3.60/1.03  ac_symbols:                             0
% 3.60/1.03  
% 3.60/1.03  ------ Propositional Solver
% 3.60/1.03  
% 3.60/1.03  prop_solver_calls:                      30
% 3.60/1.03  prop_fast_solver_calls:                 617
% 3.60/1.03  smt_solver_calls:                       0
% 3.60/1.03  smt_fast_solver_calls:                  0
% 3.60/1.03  prop_num_of_clauses:                    3177
% 3.60/1.03  prop_preprocess_simplified:             6492
% 3.60/1.03  prop_fo_subsumed:                       9
% 3.60/1.03  prop_solver_time:                       0.
% 3.60/1.03  smt_solver_time:                        0.
% 3.60/1.03  smt_fast_solver_time:                   0.
% 3.60/1.03  prop_fast_solver_time:                  0.
% 3.60/1.03  prop_unsat_core_time:                   0.
% 3.60/1.03  
% 3.60/1.03  ------ QBF
% 3.60/1.03  
% 3.60/1.03  qbf_q_res:                              0
% 3.60/1.03  qbf_num_tautologies:                    0
% 3.60/1.03  qbf_prep_cycles:                        0
% 3.60/1.03  
% 3.60/1.03  ------ BMC1
% 3.60/1.03  
% 3.60/1.03  bmc1_current_bound:                     -1
% 3.60/1.03  bmc1_last_solved_bound:                 -1
% 3.60/1.03  bmc1_unsat_core_size:                   -1
% 3.60/1.03  bmc1_unsat_core_parents_size:           -1
% 3.60/1.03  bmc1_merge_next_fun:                    0
% 3.60/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.60/1.03  
% 3.60/1.03  ------ Instantiation
% 3.60/1.03  
% 3.60/1.03  inst_num_of_clauses:                    997
% 3.60/1.03  inst_num_in_passive:                    224
% 3.60/1.03  inst_num_in_active:                     373
% 3.60/1.03  inst_num_in_unprocessed:                400
% 3.60/1.03  inst_num_of_loops:                      410
% 3.60/1.03  inst_num_of_learning_restarts:          0
% 3.60/1.03  inst_num_moves_active_passive:          32
% 3.60/1.03  inst_lit_activity:                      0
% 3.60/1.03  inst_lit_activity_moves:                0
% 3.60/1.03  inst_num_tautologies:                   0
% 3.60/1.03  inst_num_prop_implied:                  0
% 3.60/1.03  inst_num_existing_simplified:           0
% 3.60/1.03  inst_num_eq_res_simplified:             0
% 3.60/1.03  inst_num_child_elim:                    0
% 3.60/1.03  inst_num_of_dismatching_blockings:      413
% 3.60/1.03  inst_num_of_non_proper_insts:           929
% 3.60/1.03  inst_num_of_duplicates:                 0
% 3.60/1.03  inst_inst_num_from_inst_to_res:         0
% 3.60/1.03  inst_dismatching_checking_time:         0.
% 3.60/1.03  
% 3.60/1.03  ------ Resolution
% 3.60/1.03  
% 3.60/1.03  res_num_of_clauses:                     0
% 3.60/1.03  res_num_in_passive:                     0
% 3.60/1.03  res_num_in_active:                      0
% 3.60/1.03  res_num_of_loops:                       114
% 3.60/1.03  res_forward_subset_subsumed:            187
% 3.60/1.03  res_backward_subset_subsumed:           0
% 3.60/1.03  res_forward_subsumed:                   0
% 3.60/1.03  res_backward_subsumed:                  0
% 3.60/1.03  res_forward_subsumption_resolution:     0
% 3.60/1.03  res_backward_subsumption_resolution:    0
% 3.60/1.03  res_clause_to_clause_subsumption:       1435
% 3.60/1.03  res_orphan_elimination:                 0
% 3.60/1.03  res_tautology_del:                      186
% 3.60/1.03  res_num_eq_res_simplified:              0
% 3.60/1.03  res_num_sel_changes:                    0
% 3.60/1.03  res_moves_from_active_to_pass:          0
% 3.60/1.03  
% 3.60/1.03  ------ Superposition
% 3.60/1.03  
% 3.60/1.03  sup_time_total:                         0.
% 3.60/1.03  sup_time_generating:                    0.
% 3.60/1.03  sup_time_sim_full:                      0.
% 3.60/1.03  sup_time_sim_immed:                     0.
% 3.60/1.03  
% 3.60/1.03  sup_num_of_clauses:                     246
% 3.60/1.03  sup_num_in_active:                      69
% 3.60/1.03  sup_num_in_passive:                     177
% 3.60/1.03  sup_num_of_loops:                       80
% 3.60/1.03  sup_fw_superposition:                   409
% 3.60/1.03  sup_bw_superposition:                   302
% 3.60/1.03  sup_immediate_simplified:               237
% 3.60/1.03  sup_given_eliminated:                   2
% 3.60/1.03  comparisons_done:                       0
% 3.60/1.03  comparisons_avoided:                    0
% 3.60/1.03  
% 3.60/1.03  ------ Simplifications
% 3.60/1.03  
% 3.60/1.03  
% 3.60/1.03  sim_fw_subset_subsumed:                 29
% 3.60/1.03  sim_bw_subset_subsumed:                 2
% 3.60/1.03  sim_fw_subsumed:                        83
% 3.60/1.03  sim_bw_subsumed:                        3
% 3.60/1.03  sim_fw_subsumption_res:                 0
% 3.60/1.03  sim_bw_subsumption_res:                 0
% 3.60/1.03  sim_tautology_del:                      9
% 3.60/1.03  sim_eq_tautology_del:                   33
% 3.60/1.03  sim_eq_res_simp:                        1
% 3.60/1.03  sim_fw_demodulated:                     123
% 3.60/1.03  sim_bw_demodulated:                     32
% 3.60/1.03  sim_light_normalised:                   63
% 3.60/1.03  sim_joinable_taut:                      0
% 3.60/1.03  sim_joinable_simp:                      0
% 3.60/1.03  sim_ac_normalised:                      0
% 3.60/1.03  sim_smt_subsumption:                    0
% 3.60/1.03  
%------------------------------------------------------------------------------

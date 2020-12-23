%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:53 EST 2020

% Result     : Theorem 19.69s
% Output     : CNFRefutation 19.69s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 454 expanded)
%              Number of clauses        :   66 ( 135 expanded)
%              Number of leaves         :   15 ( 127 expanded)
%              Depth                    :   19
%              Number of atoms          :  359 (2524 expanded)
%              Number of equality atoms :  127 ( 537 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f2])).

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
    inference(flattening,[],[f22])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
          & v3_pre_topc(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X0,sK3) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK3,X1))
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))
    & v3_pre_topc(sK3,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & v1_tops_1(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f30,f29,f28])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    v1_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_855,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_854,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_847,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_849,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1464,plain,
    ( r2_hidden(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_849])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_856,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4932,plain,
    ( k3_xboole_0(u1_struct_0(sK1),X0) = X1
    | r2_hidden(sK0(u1_struct_0(sK1),X0,X1),X1) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),X0,X1),X0) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),X0,X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_856])).

cnf(c_14828,plain,
    ( k3_xboole_0(u1_struct_0(sK1),X0) = sK3
    | r2_hidden(sK0(u1_struct_0(sK1),X0,sK3),X0) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),X0,sK3),u1_struct_0(sK1)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),X0,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_4932])).

cnf(c_23669,plain,
    ( k3_xboole_0(u1_struct_0(sK1),sK3) = sK3
    | r2_hidden(sK0(u1_struct_0(sK1),sK3,sK3),u1_struct_0(sK1)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),sK3,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_14828])).

cnf(c_69505,plain,
    ( k3_xboole_0(u1_struct_0(sK1),sK3) = sK3
    | r2_hidden(sK0(u1_struct_0(sK1),sK3,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_23669,c_856])).

cnf(c_69896,plain,
    ( k3_xboole_0(u1_struct_0(sK1),sK3) = sK3
    | r2_hidden(sK0(u1_struct_0(sK1),sK3,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_69505])).

cnf(c_69918,plain,
    ( k3_xboole_0(u1_struct_0(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_69896,c_69505])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_69923,plain,
    ( k3_xboole_0(sK3,u1_struct_0(sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_69918,c_0])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_850,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_848,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1352,plain,
    ( k9_subset_1(X0,X1,k2_subset_1(X0)) = k3_xboole_0(X1,k2_subset_1(X0)) ),
    inference(superposition,[status(thm)],[c_850,c_848])).

cnf(c_2759,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,k2_subset_1(X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1352])).

cnf(c_1053,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_850])).

cnf(c_1355,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1053,c_848])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_225,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_260,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_225,c_21])).

cnf(c_261,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2))
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_244,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_240,c_22,c_21,c_18])).

cnf(c_845,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_1237,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,u1_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,u1_struct_0(sK1))) ),
    inference(superposition,[status(thm)],[c_1053,c_845])).

cnf(c_1234,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,k2_subset_1(u1_struct_0(sK1))))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_subset_1(u1_struct_0(sK1)))) ),
    inference(superposition,[status(thm)],[c_850,c_845])).

cnf(c_2267,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,u1_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_subset_1(u1_struct_0(sK1)))) ),
    inference(superposition,[status(thm)],[c_7,c_1234])).

cnf(c_3651,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_subset_1(u1_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,u1_struct_0(sK1))) ),
    inference(superposition,[status(thm)],[c_1237,c_2267])).

cnf(c_12103,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_subset_1(k2_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,u1_struct_0(sK1))) ),
    inference(superposition,[status(thm)],[c_261,c_3651])).

cnf(c_19852,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,u1_struct_0(sK1))) ),
    inference(superposition,[status(thm)],[c_7,c_12103])).

cnf(c_20111,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k3_xboole_0(sK3,u1_struct_0(sK1))) ),
    inference(superposition,[status(thm)],[c_1355,c_19852])).

cnf(c_20114,plain,
    ( k2_pre_topc(sK1,k3_xboole_0(sK3,k2_subset_1(k2_struct_0(sK1)))) = k2_pre_topc(sK1,k3_xboole_0(sK3,u1_struct_0(sK1))) ),
    inference(superposition,[status(thm)],[c_2759,c_20111])).

cnf(c_19,negated_conjecture,
    ( v1_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_265,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_266,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_266])).

cnf(c_306,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_308,plain,
    ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_20])).

cnf(c_846,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1236,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_846,c_845])).

cnf(c_3093,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_261,c_1236])).

cnf(c_10140,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_308,c_3093])).

cnf(c_18512,plain,
    ( k2_pre_topc(sK1,k3_xboole_0(sK3,k2_subset_1(k2_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_2759,c_10140])).

cnf(c_16,negated_conjecture,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18516,plain,
    ( k2_pre_topc(sK1,k3_xboole_0(sK3,k2_subset_1(k2_struct_0(sK1)))) != k2_pre_topc(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_18512,c_16])).

cnf(c_20240,plain,
    ( k2_pre_topc(sK1,k3_xboole_0(sK3,u1_struct_0(sK1))) != k2_pre_topc(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_20114,c_18516])).

cnf(c_70201,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_69923,c_20240])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 19.69/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.69/3.00  
% 19.69/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.69/3.00  
% 19.69/3.00  ------  iProver source info
% 19.69/3.00  
% 19.69/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.69/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.69/3.00  git: non_committed_changes: false
% 19.69/3.00  git: last_make_outside_of_git: false
% 19.69/3.00  
% 19.69/3.00  ------ 
% 19.69/3.00  ------ Parsing...
% 19.69/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.69/3.00  
% 19.69/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 19.69/3.00  
% 19.69/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.69/3.00  
% 19.69/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.69/3.00  ------ Proving...
% 19.69/3.00  ------ Problem Properties 
% 19.69/3.00  
% 19.69/3.00  
% 19.69/3.00  clauses                                 17
% 19.69/3.00  conjectures                             3
% 19.69/3.00  EPR                                     0
% 19.69/3.00  Horn                                    15
% 19.69/3.00  unary                                   8
% 19.69/3.00  binary                                  4
% 19.69/3.00  lits                                    32
% 19.69/3.00  lits eq                                 10
% 19.69/3.00  fd_pure                                 0
% 19.69/3.00  fd_pseudo                               0
% 19.69/3.00  fd_cond                                 0
% 19.69/3.00  fd_pseudo_cond                          3
% 19.69/3.00  AC symbols                              0
% 19.69/3.00  
% 19.69/3.00  ------ Input Options Time Limit: Unbounded
% 19.69/3.00  
% 19.69/3.00  
% 19.69/3.00  ------ 
% 19.69/3.00  Current options:
% 19.69/3.00  ------ 
% 19.69/3.00  
% 19.69/3.00  
% 19.69/3.00  
% 19.69/3.00  
% 19.69/3.00  ------ Proving...
% 19.69/3.00  
% 19.69/3.00  
% 19.69/3.00  % SZS status Theorem for theBenchmark.p
% 19.69/3.00  
% 19.69/3.00   Resolution empty clause
% 19.69/3.00  
% 19.69/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.69/3.00  
% 19.69/3.00  fof(f2,axiom,(
% 19.69/3.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f22,plain,(
% 19.69/3.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.69/3.00    inference(nnf_transformation,[],[f2])).
% 19.69/3.00  
% 19.69/3.00  fof(f23,plain,(
% 19.69/3.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.69/3.00    inference(flattening,[],[f22])).
% 19.69/3.00  
% 19.69/3.00  fof(f24,plain,(
% 19.69/3.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.69/3.00    inference(rectify,[],[f23])).
% 19.69/3.00  
% 19.69/3.00  fof(f25,plain,(
% 19.69/3.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.69/3.00    introduced(choice_axiom,[])).
% 19.69/3.00  
% 19.69/3.00  fof(f26,plain,(
% 19.69/3.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.69/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 19.69/3.00  
% 19.69/3.00  fof(f37,plain,(
% 19.69/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.69/3.00    inference(cnf_transformation,[],[f26])).
% 19.69/3.00  
% 19.69/3.00  fof(f36,plain,(
% 19.69/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.69/3.00    inference(cnf_transformation,[],[f26])).
% 19.69/3.00  
% 19.69/3.00  fof(f11,conjecture,(
% 19.69/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f12,negated_conjecture,(
% 19.69/3.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 19.69/3.00    inference(negated_conjecture,[],[f11])).
% 19.69/3.00  
% 19.69/3.00  fof(f20,plain,(
% 19.69/3.00    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 19.69/3.00    inference(ennf_transformation,[],[f12])).
% 19.69/3.00  
% 19.69/3.00  fof(f21,plain,(
% 19.69/3.00    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.69/3.00    inference(flattening,[],[f20])).
% 19.69/3.00  
% 19.69/3.00  fof(f30,plain,(
% 19.69/3.00    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_pre_topc(X0,sK3) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK3,X1)) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.69/3.00    introduced(choice_axiom,[])).
% 19.69/3.00  
% 19.69/3.00  fof(f29,plain,(
% 19.69/3.00    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,sK2)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.69/3.00    introduced(choice_axiom,[])).
% 19.69/3.00  
% 19.69/3.00  fof(f28,plain,(
% 19.69/3.00    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1)) & v3_pre_topc(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 19.69/3.00    introduced(choice_axiom,[])).
% 19.69/3.00  
% 19.69/3.00  fof(f31,plain,(
% 19.69/3.00    ((k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) & v3_pre_topc(sK3,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 19.69/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f30,f29,f28])).
% 19.69/3.00  
% 19.69/3.00  fof(f52,plain,(
% 19.69/3.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.69/3.00    inference(cnf_transformation,[],[f31])).
% 19.69/3.00  
% 19.69/3.00  fof(f5,axiom,(
% 19.69/3.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f13,plain,(
% 19.69/3.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.69/3.00    inference(ennf_transformation,[],[f5])).
% 19.69/3.00  
% 19.69/3.00  fof(f41,plain,(
% 19.69/3.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.69/3.00    inference(cnf_transformation,[],[f13])).
% 19.69/3.00  
% 19.69/3.00  fof(f38,plain,(
% 19.69/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.69/3.00    inference(cnf_transformation,[],[f26])).
% 19.69/3.00  
% 19.69/3.00  fof(f1,axiom,(
% 19.69/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f32,plain,(
% 19.69/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.69/3.00    inference(cnf_transformation,[],[f1])).
% 19.69/3.00  
% 19.69/3.00  fof(f3,axiom,(
% 19.69/3.00    ! [X0] : k2_subset_1(X0) = X0),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f39,plain,(
% 19.69/3.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 19.69/3.00    inference(cnf_transformation,[],[f3])).
% 19.69/3.00  
% 19.69/3.00  fof(f4,axiom,(
% 19.69/3.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f40,plain,(
% 19.69/3.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 19.69/3.00    inference(cnf_transformation,[],[f4])).
% 19.69/3.00  
% 19.69/3.00  fof(f6,axiom,(
% 19.69/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f14,plain,(
% 19.69/3.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.69/3.00    inference(ennf_transformation,[],[f6])).
% 19.69/3.00  
% 19.69/3.00  fof(f42,plain,(
% 19.69/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.69/3.00    inference(cnf_transformation,[],[f14])).
% 19.69/3.00  
% 19.69/3.00  fof(f8,axiom,(
% 19.69/3.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f16,plain,(
% 19.69/3.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.69/3.00    inference(ennf_transformation,[],[f8])).
% 19.69/3.00  
% 19.69/3.00  fof(f44,plain,(
% 19.69/3.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.69/3.00    inference(cnf_transformation,[],[f16])).
% 19.69/3.00  
% 19.69/3.00  fof(f7,axiom,(
% 19.69/3.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f15,plain,(
% 19.69/3.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 19.69/3.00    inference(ennf_transformation,[],[f7])).
% 19.69/3.00  
% 19.69/3.00  fof(f43,plain,(
% 19.69/3.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 19.69/3.00    inference(cnf_transformation,[],[f15])).
% 19.69/3.00  
% 19.69/3.00  fof(f49,plain,(
% 19.69/3.00    l1_pre_topc(sK1)),
% 19.69/3.00    inference(cnf_transformation,[],[f31])).
% 19.69/3.00  
% 19.69/3.00  fof(f10,axiom,(
% 19.69/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))))))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f18,plain,(
% 19.69/3.00    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.69/3.00    inference(ennf_transformation,[],[f10])).
% 19.69/3.00  
% 19.69/3.00  fof(f19,plain,(
% 19.69/3.00    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.69/3.00    inference(flattening,[],[f18])).
% 19.69/3.00  
% 19.69/3.00  fof(f47,plain,(
% 19.69/3.00    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.69/3.00    inference(cnf_transformation,[],[f19])).
% 19.69/3.00  
% 19.69/3.00  fof(f53,plain,(
% 19.69/3.00    v3_pre_topc(sK3,sK1)),
% 19.69/3.00    inference(cnf_transformation,[],[f31])).
% 19.69/3.00  
% 19.69/3.00  fof(f48,plain,(
% 19.69/3.00    v2_pre_topc(sK1)),
% 19.69/3.00    inference(cnf_transformation,[],[f31])).
% 19.69/3.00  
% 19.69/3.00  fof(f51,plain,(
% 19.69/3.00    v1_tops_1(sK2,sK1)),
% 19.69/3.00    inference(cnf_transformation,[],[f31])).
% 19.69/3.00  
% 19.69/3.00  fof(f9,axiom,(
% 19.69/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 19.69/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.69/3.00  
% 19.69/3.00  fof(f17,plain,(
% 19.69/3.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.69/3.00    inference(ennf_transformation,[],[f9])).
% 19.69/3.00  
% 19.69/3.00  fof(f27,plain,(
% 19.69/3.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.69/3.00    inference(nnf_transformation,[],[f17])).
% 19.69/3.00  
% 19.69/3.00  fof(f45,plain,(
% 19.69/3.00    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.69/3.00    inference(cnf_transformation,[],[f27])).
% 19.69/3.00  
% 19.69/3.00  fof(f50,plain,(
% 19.69/3.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.69/3.00    inference(cnf_transformation,[],[f31])).
% 19.69/3.00  
% 19.69/3.00  fof(f54,plain,(
% 19.69/3.00    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))),
% 19.69/3.00    inference(cnf_transformation,[],[f31])).
% 19.69/3.00  
% 19.69/3.00  cnf(c_2,plain,
% 19.69/3.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.69/3.00      | k3_xboole_0(X0,X1) = X2 ),
% 19.69/3.00      inference(cnf_transformation,[],[f37]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_855,plain,
% 19.69/3.00      ( k3_xboole_0(X0,X1) = X2
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_3,plain,
% 19.69/3.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.69/3.00      | k3_xboole_0(X0,X1) = X2 ),
% 19.69/3.00      inference(cnf_transformation,[],[f36]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_854,plain,
% 19.69/3.00      ( k3_xboole_0(X0,X1) = X2
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_18,negated_conjecture,
% 19.69/3.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.69/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_847,plain,
% 19.69/3.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_9,plain,
% 19.69/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.69/3.00      | ~ r2_hidden(X2,X0)
% 19.69/3.00      | r2_hidden(X2,X1) ),
% 19.69/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_849,plain,
% 19.69/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.69/3.00      | r2_hidden(X2,X0) != iProver_top
% 19.69/3.00      | r2_hidden(X2,X1) = iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_1464,plain,
% 19.69/3.00      ( r2_hidden(X0,u1_struct_0(sK1)) = iProver_top
% 19.69/3.00      | r2_hidden(X0,sK3) != iProver_top ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_847,c_849]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_1,plain,
% 19.69/3.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 19.69/3.00      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 19.69/3.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 19.69/3.00      | k3_xboole_0(X0,X1) = X2 ),
% 19.69/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_856,plain,
% 19.69/3.00      ( k3_xboole_0(X0,X1) = X2
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 19.69/3.00      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_4932,plain,
% 19.69/3.00      ( k3_xboole_0(u1_struct_0(sK1),X0) = X1
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),X0,X1),X1) != iProver_top
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),X0,X1),X0) != iProver_top
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),X0,X1),sK3) != iProver_top ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_1464,c_856]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_14828,plain,
% 19.69/3.00      ( k3_xboole_0(u1_struct_0(sK1),X0) = sK3
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),X0,sK3),X0) != iProver_top
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),X0,sK3),u1_struct_0(sK1)) = iProver_top
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),X0,sK3),sK3) != iProver_top ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_854,c_4932]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_23669,plain,
% 19.69/3.00      ( k3_xboole_0(u1_struct_0(sK1),sK3) = sK3
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),sK3,sK3),u1_struct_0(sK1)) = iProver_top
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),sK3,sK3),sK3) != iProver_top ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_854,c_14828]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_69505,plain,
% 19.69/3.00      ( k3_xboole_0(u1_struct_0(sK1),sK3) = sK3
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),sK3,sK3),sK3) != iProver_top ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_23669,c_856]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_69896,plain,
% 19.69/3.00      ( k3_xboole_0(u1_struct_0(sK1),sK3) = sK3
% 19.69/3.00      | r2_hidden(sK0(u1_struct_0(sK1),sK3,sK3),sK3) = iProver_top ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_855,c_69505]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_69918,plain,
% 19.69/3.00      ( k3_xboole_0(u1_struct_0(sK1),sK3) = sK3 ),
% 19.69/3.00      inference(global_propositional_subsumption,
% 19.69/3.00                [status(thm)],
% 19.69/3.00                [c_69896,c_69505]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_0,plain,
% 19.69/3.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.69/3.00      inference(cnf_transformation,[],[f32]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_69923,plain,
% 19.69/3.00      ( k3_xboole_0(sK3,u1_struct_0(sK1)) = sK3 ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_69918,c_0]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_7,plain,
% 19.69/3.00      ( k2_subset_1(X0) = X0 ),
% 19.69/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_8,plain,
% 19.69/3.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 19.69/3.00      inference(cnf_transformation,[],[f40]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_850,plain,
% 19.69/3.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_10,plain,
% 19.69/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.69/3.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 19.69/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_848,plain,
% 19.69/3.00      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 19.69/3.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_1352,plain,
% 19.69/3.00      ( k9_subset_1(X0,X1,k2_subset_1(X0)) = k3_xboole_0(X1,k2_subset_1(X0)) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_850,c_848]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_2759,plain,
% 19.69/3.00      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,k2_subset_1(X0)) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_7,c_1352]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_1053,plain,
% 19.69/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_7,c_850]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_1355,plain,
% 19.69/3.00      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_1053,c_848]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_12,plain,
% 19.69/3.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 19.69/3.00      inference(cnf_transformation,[],[f44]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_11,plain,
% 19.69/3.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 19.69/3.00      inference(cnf_transformation,[],[f43]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_225,plain,
% 19.69/3.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 19.69/3.00      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_21,negated_conjecture,
% 19.69/3.00      ( l1_pre_topc(sK1) ),
% 19.69/3.00      inference(cnf_transformation,[],[f49]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_260,plain,
% 19.69/3.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 19.69/3.00      inference(resolution_lifted,[status(thm)],[c_225,c_21]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_261,plain,
% 19.69/3.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 19.69/3.00      inference(unflattening,[status(thm)],[c_260]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_15,plain,
% 19.69/3.00      ( ~ v3_pre_topc(X0,X1)
% 19.69/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.00      | ~ v2_pre_topc(X1)
% 19.69/3.00      | ~ l1_pre_topc(X1)
% 19.69/3.00      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) ),
% 19.69/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_17,negated_conjecture,
% 19.69/3.00      ( v3_pre_topc(sK3,sK1) ),
% 19.69/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_239,plain,
% 19.69/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.00      | ~ v2_pre_topc(X1)
% 19.69/3.00      | ~ l1_pre_topc(X1)
% 19.69/3.00      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2))
% 19.69/3.00      | sK3 != X0
% 19.69/3.00      | sK1 != X1 ),
% 19.69/3.00      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_240,plain,
% 19.69/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.00      | ~ v2_pre_topc(sK1)
% 19.69/3.00      | ~ l1_pre_topc(sK1)
% 19.69/3.00      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
% 19.69/3.00      inference(unflattening,[status(thm)],[c_239]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_22,negated_conjecture,
% 19.69/3.00      ( v2_pre_topc(sK1) ),
% 19.69/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_244,plain,
% 19.69/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.00      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
% 19.69/3.00      inference(global_propositional_subsumption,
% 19.69/3.00                [status(thm)],
% 19.69/3.00                [c_240,c_22,c_21,c_18]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_845,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0))
% 19.69/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_244]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_1237,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,u1_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,u1_struct_0(sK1))) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_1053,c_845]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_1234,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,k2_subset_1(u1_struct_0(sK1))))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_subset_1(u1_struct_0(sK1)))) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_850,c_845]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_2267,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,u1_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_subset_1(u1_struct_0(sK1)))) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_7,c_1234]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_3651,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_subset_1(u1_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,u1_struct_0(sK1))) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_1237,c_2267]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_12103,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_subset_1(k2_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,u1_struct_0(sK1))) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_261,c_3651]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_19852,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,u1_struct_0(sK1))) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_7,c_12103]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_20111,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k3_xboole_0(sK3,u1_struct_0(sK1))) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_1355,c_19852]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_20114,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k3_xboole_0(sK3,k2_subset_1(k2_struct_0(sK1)))) = k2_pre_topc(sK1,k3_xboole_0(sK3,u1_struct_0(sK1))) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_2759,c_20111]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_19,negated_conjecture,
% 19.69/3.00      ( v1_tops_1(sK2,sK1) ),
% 19.69/3.00      inference(cnf_transformation,[],[f51]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_14,plain,
% 19.69/3.00      ( ~ v1_tops_1(X0,X1)
% 19.69/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.00      | ~ l1_pre_topc(X1)
% 19.69/3.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 19.69/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_265,plain,
% 19.69/3.00      ( ~ v1_tops_1(X0,X1)
% 19.69/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 19.69/3.00      | sK1 != X1 ),
% 19.69/3.00      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_266,plain,
% 19.69/3.00      ( ~ v1_tops_1(X0,sK1)
% 19.69/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.00      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
% 19.69/3.00      inference(unflattening,[status(thm)],[c_265]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_305,plain,
% 19.69/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.00      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
% 19.69/3.00      | sK2 != X0
% 19.69/3.00      | sK1 != sK1 ),
% 19.69/3.00      inference(resolution_lifted,[status(thm)],[c_19,c_266]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_306,plain,
% 19.69/3.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.00      | k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
% 19.69/3.00      inference(unflattening,[status(thm)],[c_305]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_20,negated_conjecture,
% 19.69/3.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.69/3.00      inference(cnf_transformation,[],[f50]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_308,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
% 19.69/3.00      inference(global_propositional_subsumption,[status(thm)],[c_306,c_20]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_846,plain,
% 19.69/3.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.69/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_1236,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_846,c_845]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_3093,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_261,c_1236]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_10140,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_308,c_3093]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_18512,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k3_xboole_0(sK3,k2_subset_1(k2_struct_0(sK1)))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_2759,c_10140]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_16,negated_conjecture,
% 19.69/3.00      ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
% 19.69/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_18516,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k3_xboole_0(sK3,k2_subset_1(k2_struct_0(sK1)))) != k2_pre_topc(sK1,sK3) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_18512,c_16]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_20240,plain,
% 19.69/3.00      ( k2_pre_topc(sK1,k3_xboole_0(sK3,u1_struct_0(sK1))) != k2_pre_topc(sK1,sK3) ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_20114,c_18516]) ).
% 19.69/3.00  
% 19.69/3.00  cnf(c_70201,plain,
% 19.69/3.00      ( $false ),
% 19.69/3.00      inference(superposition,[status(thm)],[c_69923,c_20240]) ).
% 19.69/3.00  
% 19.69/3.00  
% 19.69/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.69/3.00  
% 19.69/3.00  ------                               Statistics
% 19.69/3.00  
% 19.69/3.00  ------ Selected
% 19.69/3.00  
% 19.69/3.00  total_time:                             2.08
% 19.69/3.00  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:42 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 985 expanded)
%              Number of clauses        :   93 ( 307 expanded)
%              Number of leaves         :   16 ( 207 expanded)
%              Depth                    :   20
%              Number of atoms          :  396 (4407 expanded)
%              Number of equality atoms :  197 (1330 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1)
          | ~ v4_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
            | ~ v4_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_734,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_743,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1207,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_743])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_744,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_738,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1347,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_738])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_135,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_136,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_135])).

cnf(c_172,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_136])).

cnf(c_730,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_2327,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k2_tops_1(X1,X0))) = k2_tops_1(X1,X0)
    | v4_pre_topc(X0,X1) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1347,c_730])).

cnf(c_10670,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_2327])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_174,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_136])).

cnf(c_728,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_3610,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1207,c_728])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_737,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1492,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_737])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1560,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1492,c_18,c_17,c_1000])).

cnf(c_4033,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3610,c_1560])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_745,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_171,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_136])).

cnf(c_731,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_3208,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_745,c_731])).

cnf(c_4252,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4033,c_3208])).

cnf(c_4262,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_4252,c_4033])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_735,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_741,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2143,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_741])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2546,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2143,c_21])).

cnf(c_2547,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2546])).

cnf(c_2552,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_735,c_2547])).

cnf(c_4031,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3610,c_2552])).

cnf(c_6937,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4031,c_745])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_974,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_975,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_974])).

cnf(c_1202,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_738])).

cnf(c_1564,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1202,c_21])).

cnf(c_1565,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1564])).

cnf(c_7674,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6937,c_20,c_21,c_22,c_975,c_1565])).

cnf(c_7682,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7674,c_731])).

cnf(c_7690,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_7682,c_4033])).

cnf(c_10674,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10670,c_4262,c_7690])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_740,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_743])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_136])).

cnf(c_729,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_3758,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_729])).

cnf(c_4806,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_3758])).

cnf(c_5118,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_4806])).

cnf(c_9024,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5118,c_21])).

cnf(c_9025,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9024])).

cnf(c_9034,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_734,c_9025])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_739,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2112,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_739])).

cnf(c_977,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2542,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2112,c_18,c_17,c_977])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_746,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1570,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_746])).

cnf(c_1725,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_735,c_1570])).

cnf(c_4032,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3610,c_1725])).

cnf(c_1060,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_745,c_746])).

cnf(c_6936,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4031,c_1060])).

cnf(c_6972,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4032,c_20,c_21,c_22,c_975,c_1570,c_6936])).

cnf(c_6976,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_6972])).

cnf(c_9036,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_9034,c_2542,c_6976])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_736,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4015,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3610,c_736])).

cnf(c_4025,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4015])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10674,c_9036,c_4025,c_975,c_974,c_22,c_17,c_21,c_18,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.48/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.01  
% 3.48/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/1.01  
% 3.48/1.01  ------  iProver source info
% 3.48/1.01  
% 3.48/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.48/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/1.01  git: non_committed_changes: false
% 3.48/1.01  git: last_make_outside_of_git: false
% 3.48/1.01  
% 3.48/1.01  ------ 
% 3.48/1.01  ------ Parsing...
% 3.48/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.01  ------ Proving...
% 3.48/1.01  ------ Problem Properties 
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  clauses                                 20
% 3.48/1.01  conjectures                             5
% 3.48/1.01  EPR                                     2
% 3.48/1.01  Horn                                    19
% 3.48/1.01  unary                                   5
% 3.48/1.01  binary                                  8
% 3.48/1.01  lits                                    46
% 3.48/1.01  lits eq                                 12
% 3.48/1.01  fd_pure                                 0
% 3.48/1.01  fd_pseudo                               0
% 3.48/1.01  fd_cond                                 0
% 3.48/1.01  fd_pseudo_cond                          0
% 3.48/1.01  AC symbols                              0
% 3.48/1.01  
% 3.48/1.01  ------ Input Options Time Limit: Unbounded
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  ------ 
% 3.48/1.01  Current options:
% 3.48/1.01  ------ 
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  ------ Proving...
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  % SZS status Theorem for theBenchmark.p
% 3.48/1.01  
% 3.48/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/1.01  
% 3.48/1.01  fof(f14,conjecture,(
% 3.48/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f15,negated_conjecture,(
% 3.48/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.48/1.01    inference(negated_conjecture,[],[f14])).
% 3.48/1.01  
% 3.48/1.01  fof(f30,plain,(
% 3.48/1.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.48/1.01    inference(ennf_transformation,[],[f15])).
% 3.48/1.01  
% 3.48/1.01  fof(f31,plain,(
% 3.48/1.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.48/1.01    inference(flattening,[],[f30])).
% 3.48/1.01  
% 3.48/1.01  fof(f33,plain,(
% 3.48/1.01    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.48/1.01    inference(nnf_transformation,[],[f31])).
% 3.48/1.01  
% 3.48/1.01  fof(f34,plain,(
% 3.48/1.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.48/1.01    inference(flattening,[],[f33])).
% 3.48/1.01  
% 3.48/1.01  fof(f36,plain,(
% 3.48/1.01    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.48/1.01    introduced(choice_axiom,[])).
% 3.48/1.01  
% 3.48/1.01  fof(f35,plain,(
% 3.48/1.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.48/1.01    introduced(choice_axiom,[])).
% 3.48/1.01  
% 3.48/1.01  fof(f37,plain,(
% 3.48/1.01    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.48/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 3.48/1.01  
% 3.48/1.01  fof(f55,plain,(
% 3.48/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.48/1.01    inference(cnf_transformation,[],[f37])).
% 3.48/1.01  
% 3.48/1.01  fof(f8,axiom,(
% 3.48/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f32,plain,(
% 3.48/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.48/1.01    inference(nnf_transformation,[],[f8])).
% 3.48/1.01  
% 3.48/1.01  fof(f45,plain,(
% 3.48/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f32])).
% 3.48/1.01  
% 3.48/1.01  fof(f46,plain,(
% 3.48/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f32])).
% 3.48/1.01  
% 3.48/1.01  fof(f12,axiom,(
% 3.48/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f27,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.48/1.01    inference(ennf_transformation,[],[f12])).
% 3.48/1.01  
% 3.48/1.01  fof(f28,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.48/1.01    inference(flattening,[],[f27])).
% 3.48/1.01  
% 3.48/1.01  fof(f51,plain,(
% 3.48/1.01    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f28])).
% 3.48/1.01  
% 3.48/1.01  fof(f5,axiom,(
% 3.48/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f18,plain,(
% 3.48/1.01    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/1.01    inference(ennf_transformation,[],[f5])).
% 3.48/1.01  
% 3.48/1.01  fof(f42,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f18])).
% 3.48/1.01  
% 3.48/1.01  fof(f7,axiom,(
% 3.48/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f21,plain,(
% 3.48/1.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/1.01    inference(ennf_transformation,[],[f7])).
% 3.48/1.01  
% 3.48/1.01  fof(f44,plain,(
% 3.48/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f21])).
% 3.48/1.01  
% 3.48/1.01  fof(f13,axiom,(
% 3.48/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f29,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.48/1.01    inference(ennf_transformation,[],[f13])).
% 3.48/1.01  
% 3.48/1.01  fof(f52,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f29])).
% 3.48/1.01  
% 3.48/1.01  fof(f54,plain,(
% 3.48/1.01    l1_pre_topc(sK0)),
% 3.48/1.01    inference(cnf_transformation,[],[f37])).
% 3.48/1.01  
% 3.48/1.01  fof(f3,axiom,(
% 3.48/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f40,plain,(
% 3.48/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f3])).
% 3.48/1.01  
% 3.48/1.01  fof(f4,axiom,(
% 3.48/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f17,plain,(
% 3.48/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/1.01    inference(ennf_transformation,[],[f4])).
% 3.48/1.01  
% 3.48/1.01  fof(f41,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f17])).
% 3.48/1.01  
% 3.48/1.01  fof(f56,plain,(
% 3.48/1.01    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.48/1.01    inference(cnf_transformation,[],[f37])).
% 3.48/1.01  
% 3.48/1.01  fof(f9,axiom,(
% 3.48/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f22,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.48/1.01    inference(ennf_transformation,[],[f9])).
% 3.48/1.01  
% 3.48/1.01  fof(f23,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.48/1.01    inference(flattening,[],[f22])).
% 3.48/1.01  
% 3.48/1.01  fof(f47,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f23])).
% 3.48/1.01  
% 3.48/1.01  fof(f53,plain,(
% 3.48/1.01    v2_pre_topc(sK0)),
% 3.48/1.01    inference(cnf_transformation,[],[f37])).
% 3.48/1.01  
% 3.48/1.01  fof(f48,plain,(
% 3.48/1.01    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f23])).
% 3.48/1.01  
% 3.48/1.01  fof(f10,axiom,(
% 3.48/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f24,plain,(
% 3.48/1.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.48/1.01    inference(ennf_transformation,[],[f10])).
% 3.48/1.01  
% 3.48/1.01  fof(f25,plain,(
% 3.48/1.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.48/1.01    inference(flattening,[],[f24])).
% 3.48/1.01  
% 3.48/1.01  fof(f49,plain,(
% 3.48/1.01    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f25])).
% 3.48/1.01  
% 3.48/1.01  fof(f6,axiom,(
% 3.48/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f19,plain,(
% 3.48/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.48/1.01    inference(ennf_transformation,[],[f6])).
% 3.48/1.01  
% 3.48/1.01  fof(f20,plain,(
% 3.48/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/1.01    inference(flattening,[],[f19])).
% 3.48/1.01  
% 3.48/1.01  fof(f43,plain,(
% 3.48/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f20])).
% 3.48/1.01  
% 3.48/1.01  fof(f11,axiom,(
% 3.48/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f26,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.48/1.01    inference(ennf_transformation,[],[f11])).
% 3.48/1.01  
% 3.48/1.01  fof(f50,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f26])).
% 3.48/1.01  
% 3.48/1.01  fof(f1,axiom,(
% 3.48/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f38,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f1])).
% 3.48/1.01  
% 3.48/1.01  fof(f2,axiom,(
% 3.48/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f16,plain,(
% 3.48/1.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.48/1.01    inference(ennf_transformation,[],[f2])).
% 3.48/1.01  
% 3.48/1.01  fof(f39,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f16])).
% 3.48/1.01  
% 3.48/1.01  fof(f57,plain,(
% 3.48/1.01    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.48/1.01    inference(cnf_transformation,[],[f37])).
% 3.48/1.01  
% 3.48/1.01  cnf(c_17,negated_conjecture,
% 3.48/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.48/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_734,plain,
% 3.48/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_8,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.48/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_743,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.48/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1207,plain,
% 3.48/1.01      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_734,c_743]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_7,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.48/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_744,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.48/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_13,plain,
% 3.48/1.01      ( ~ v4_pre_topc(X0,X1)
% 3.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/1.01      | r1_tarski(k2_tops_1(X1,X0),X0)
% 3.48/1.01      | ~ l1_pre_topc(X1) ),
% 3.48/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_738,plain,
% 3.48/1.01      ( v4_pre_topc(X0,X1) != iProver_top
% 3.48/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.48/1.01      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.48/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1347,plain,
% 3.48/1.01      ( v4_pre_topc(X0,X1) != iProver_top
% 3.48/1.01      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 3.48/1.01      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.48/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_744,c_738]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/1.01      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.48/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_135,plain,
% 3.48/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.48/1.01      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_136,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_135]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_172,plain,
% 3.48/1.01      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.48/1.01      inference(bin_hyper_res,[status(thm)],[c_4,c_136]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_730,plain,
% 3.48/1.01      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.48/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_172]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2327,plain,
% 3.48/1.01      ( k3_subset_1(X0,k3_subset_1(X0,k2_tops_1(X1,X0))) = k2_tops_1(X1,X0)
% 3.48/1.01      | v4_pre_topc(X0,X1) != iProver_top
% 3.48/1.01      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 3.48/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1347,c_730]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_10670,plain,
% 3.48/1.01      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 3.48/1.01      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.48/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1207,c_2327]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/1.01      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.48/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_174,plain,
% 3.48/1.01      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.48/1.01      inference(bin_hyper_res,[status(thm)],[c_6,c_136]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_728,plain,
% 3.48/1.01      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.48/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_3610,plain,
% 3.48/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1207,c_728]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_14,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/1.01      | ~ l1_pre_topc(X1)
% 3.48/1.01      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_737,plain,
% 3.48/1.01      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 3.48/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.48/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1492,plain,
% 3.48/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.48/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_734,c_737]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_18,negated_conjecture,
% 3.48/1.01      ( l1_pre_topc(sK0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1000,plain,
% 3.48/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.48/1.01      | ~ l1_pre_topc(sK0)
% 3.48/1.01      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1560,plain,
% 3.48/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_1492,c_18,c_17,c_1000]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4033,plain,
% 3.48/1.01      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_3610,c_1560]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2,plain,
% 3.48/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_745,plain,
% 3.48/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_3,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/1.01      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_171,plain,
% 3.48/1.01      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.48/1.01      inference(bin_hyper_res,[status(thm)],[c_3,c_136]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_731,plain,
% 3.48/1.01      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.48/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_3208,plain,
% 3.48/1.01      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_745,c_731]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4252,plain,
% 3.48/1.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_4033,c_3208]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4262,plain,
% 3.48/1.01      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 3.48/1.01      inference(light_normalisation,[status(thm)],[c_4252,c_4033]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_16,negated_conjecture,
% 3.48/1.01      ( v4_pre_topc(sK1,sK0)
% 3.48/1.01      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.48/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_735,plain,
% 3.48/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.48/1.01      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_10,plain,
% 3.48/1.01      ( ~ v4_pre_topc(X0,X1)
% 3.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/1.01      | ~ l1_pre_topc(X1)
% 3.48/1.01      | k2_pre_topc(X1,X0) = X0 ),
% 3.48/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_741,plain,
% 3.48/1.01      ( k2_pre_topc(X0,X1) = X1
% 3.48/1.01      | v4_pre_topc(X1,X0) != iProver_top
% 3.48/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.48/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2143,plain,
% 3.48/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.48/1.01      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.48/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_734,c_741]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_21,plain,
% 3.48/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2546,plain,
% 3.48/1.01      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.48/1.01      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_2143,c_21]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2547,plain,
% 3.48/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.48/1.01      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_2546]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2552,plain,
% 3.48/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.48/1.01      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_735,c_2547]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4031,plain,
% 3.48/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.48/1.01      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_3610,c_2552]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6937,plain,
% 3.48/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.48/1.01      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_4031,c_745]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_19,negated_conjecture,
% 3.48/1.01      ( v2_pre_topc(sK0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_20,plain,
% 3.48/1.01      ( v2_pre_topc(sK0) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_22,plain,
% 3.48/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_9,plain,
% 3.48/1.01      ( v4_pre_topc(X0,X1)
% 3.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/1.01      | ~ l1_pre_topc(X1)
% 3.48/1.01      | ~ v2_pre_topc(X1)
% 3.48/1.01      | k2_pre_topc(X1,X0) != X0 ),
% 3.48/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_974,plain,
% 3.48/1.01      ( v4_pre_topc(sK1,sK0)
% 3.48/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.48/1.01      | ~ l1_pre_topc(sK0)
% 3.48/1.01      | ~ v2_pre_topc(sK0)
% 3.48/1.01      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_975,plain,
% 3.48/1.01      ( k2_pre_topc(sK0,sK1) != sK1
% 3.48/1.01      | v4_pre_topc(sK1,sK0) = iProver_top
% 3.48/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.48/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.48/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_974]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1202,plain,
% 3.48/1.01      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.48/1.01      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.48/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_734,c_738]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1564,plain,
% 3.48/1.01      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.48/1.01      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_1202,c_21]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1565,plain,
% 3.48/1.01      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.48/1.01      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_1564]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_7674,plain,
% 3.48/1.01      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_6937,c_20,c_21,c_22,c_975,c_1565]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_7682,plain,
% 3.48/1.01      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_7674,c_731]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_7690,plain,
% 3.48/1.01      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.48/1.01      inference(light_normalisation,[status(thm)],[c_7682,c_4033]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_10674,plain,
% 3.48/1.01      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.48/1.01      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.48/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.48/1.01      inference(light_normalisation,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_10670,c_4262,c_7690]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_11,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/1.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/1.01      | ~ l1_pre_topc(X1) ),
% 3.48/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_740,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.48/1.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.48/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1363,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.48/1.01      | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
% 3.48/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_740,c_743]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_5,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.48/1.01      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 3.48/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_173,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/1.01      | ~ r1_tarski(X2,X1)
% 3.48/1.01      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.48/1.01      inference(bin_hyper_res,[status(thm)],[c_5,c_136]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_729,plain,
% 3.48/1.01      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 3.48/1.01      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.48/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_173]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_3758,plain,
% 3.48/1.01      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 3.48/1.01      | r1_tarski(X2,X0) != iProver_top
% 3.48/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_744,c_729]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4806,plain,
% 3.48/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 3.48/1.01      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1207,c_3758]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_5118,plain,
% 3.48/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 3.48/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.48/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1363,c_4806]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_9024,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.48/1.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_5118,c_21]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_9025,plain,
% 3.48/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 3.48/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_9024]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_9034,plain,
% 3.48/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_734,c_9025]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_12,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/1.01      | ~ l1_pre_topc(X1)
% 3.48/1.01      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_739,plain,
% 3.48/1.01      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.48/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.48/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2112,plain,
% 3.48/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.48/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_734,c_739]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_977,plain,
% 3.48/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.48/1.01      | ~ l1_pre_topc(sK0)
% 3.48/1.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2542,plain,
% 3.48/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_2112,c_18,c_17,c_977]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_0,plain,
% 3.48/1.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1,plain,
% 3.48/1.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.48/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_746,plain,
% 3.48/1.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1570,plain,
% 3.48/1.01      ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1
% 3.48/1.01      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1565,c_746]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1725,plain,
% 3.48/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.48/1.01      | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_735,c_1570]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4032,plain,
% 3.48/1.01      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.48/1.01      | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_3610,c_1725]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1060,plain,
% 3.48/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_745,c_746]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6936,plain,
% 3.48/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.48/1.01      | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_4031,c_1060]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6972,plain,
% 3.48/1.01      ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_4032,c_20,c_21,c_22,c_975,c_1570,c_6936]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6976,plain,
% 3.48/1.01      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_0,c_6972]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_9036,plain,
% 3.48/1.01      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.48/1.01      inference(light_normalisation,[status(thm)],[c_9034,c_2542,c_6976]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_15,negated_conjecture,
% 3.48/1.01      ( ~ v4_pre_topc(sK1,sK0)
% 3.48/1.01      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.48/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_736,plain,
% 3.48/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.48/1.01      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4015,plain,
% 3.48/1.01      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.48/1.01      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(demodulation,[status(thm)],[c_3610,c_736]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4025,plain,
% 3.48/1.01      ( ~ v4_pre_topc(sK1,sK0)
% 3.48/1.01      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.48/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4015]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(contradiction,plain,
% 3.48/1.01      ( $false ),
% 3.48/1.01      inference(minisat,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_10674,c_9036,c_4025,c_975,c_974,c_22,c_17,c_21,c_18,
% 3.48/1.01                 c_20,c_19]) ).
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/1.01  
% 3.48/1.01  ------                               Statistics
% 3.48/1.01  
% 3.48/1.01  ------ Selected
% 3.48/1.01  
% 3.48/1.01  total_time:                             0.341
% 3.48/1.01  
%------------------------------------------------------------------------------

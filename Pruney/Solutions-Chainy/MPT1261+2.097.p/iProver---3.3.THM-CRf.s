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
% DateTime   : Thu Dec  3 12:14:38 EST 2020

% Result     : Theorem 42.89s
% Output     : CNFRefutation 42.89s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 444 expanded)
%              Number of clauses        :   60 ( 127 expanded)
%              Number of leaves         :   16 (  98 expanded)
%              Depth                    :   22
%              Number of atoms          :  307 (1991 expanded)
%              Number of equality atoms :  145 ( 661 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f41,f41])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f21,plain,(
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
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_618,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_621,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3646,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_621])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_627,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1899,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_618,c_627])).

cnf(c_3649,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3646,c_1899])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4053,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3649,c_19])).

cnf(c_14,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_619,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_622,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1037,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_622])).

cnf(c_1282,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1037,c_19])).

cnf(c_1283,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1282])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_630,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1288,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_630])).

cnf(c_1461,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_619,c_1288])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1473,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1461,c_1])).

cnf(c_4058,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4053,c_1473])).

cnf(c_4061,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4058,c_1899])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_629,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4135,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4061,c_629])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_631,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6826,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4135,c_631])).

cnf(c_121858,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_6826])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_623,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4868,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_623])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_624,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_628,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3622,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_628])).

cnf(c_3884,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_3622])).

cnf(c_4409,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3884,c_19])).

cnf(c_4410,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4409])).

cnf(c_4418,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_618,c_4410])).

cnf(c_4871,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4868,c_4418])).

cnf(c_5371,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4871,c_19])).

cnf(c_122257,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_121858,c_5371])).

cnf(c_13,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_620,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2438,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1899,c_620])).

cnf(c_7,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_840,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_841,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_122257,c_4061,c_2438,c_841,c_20,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:42:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 42.89/5.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.89/5.98  
% 42.89/5.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 42.89/5.98  
% 42.89/5.98  ------  iProver source info
% 42.89/5.98  
% 42.89/5.98  git: date: 2020-06-30 10:37:57 +0100
% 42.89/5.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 42.89/5.98  git: non_committed_changes: false
% 42.89/5.98  git: last_make_outside_of_git: false
% 42.89/5.98  
% 42.89/5.98  ------ 
% 42.89/5.98  ------ Parsing...
% 42.89/5.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 42.89/5.98  
% 42.89/5.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 42.89/5.98  
% 42.89/5.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 42.89/5.98  
% 42.89/5.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 42.89/5.98  ------ Proving...
% 42.89/5.98  ------ Problem Properties 
% 42.89/5.98  
% 42.89/5.98  
% 42.89/5.98  clauses                                 18
% 42.89/5.98  conjectures                             5
% 42.89/5.98  EPR                                     2
% 42.89/5.98  Horn                                    17
% 42.89/5.98  unary                                   6
% 42.89/5.98  binary                                  5
% 42.89/5.98  lits                                    41
% 42.89/5.98  lits eq                                 12
% 42.89/5.98  fd_pure                                 0
% 42.89/5.98  fd_pseudo                               0
% 42.89/5.98  fd_cond                                 0
% 42.89/5.98  fd_pseudo_cond                          0
% 42.89/5.98  AC symbols                              0
% 42.89/5.98  
% 42.89/5.98  ------ Input Options Time Limit: Unbounded
% 42.89/5.98  
% 42.89/5.98  
% 42.89/5.98  ------ 
% 42.89/5.98  Current options:
% 42.89/5.98  ------ 
% 42.89/5.98  
% 42.89/5.98  
% 42.89/5.98  
% 42.89/5.98  
% 42.89/5.98  ------ Proving...
% 42.89/5.98  
% 42.89/5.98  
% 42.89/5.98  % SZS status Theorem for theBenchmark.p
% 42.89/5.98  
% 42.89/5.98  % SZS output start CNFRefutation for theBenchmark.p
% 42.89/5.98  
% 42.89/5.98  fof(f1,axiom,(
% 42.89/5.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 42.89/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.98  
% 42.89/5.98  fof(f36,plain,(
% 42.89/5.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 42.89/5.98    inference(cnf_transformation,[],[f1])).
% 42.89/5.98  
% 42.89/5.98  fof(f14,conjecture,(
% 42.89/5.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 42.89/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.98  
% 42.89/5.98  fof(f15,negated_conjecture,(
% 42.89/5.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 42.89/5.98    inference(negated_conjecture,[],[f14])).
% 42.89/5.98  
% 42.89/5.98  fof(f29,plain,(
% 42.89/5.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 42.89/5.98    inference(ennf_transformation,[],[f15])).
% 42.89/5.98  
% 42.89/5.98  fof(f30,plain,(
% 42.89/5.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.89/5.98    inference(flattening,[],[f29])).
% 42.89/5.98  
% 42.89/5.98  fof(f31,plain,(
% 42.89/5.98    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.89/5.98    inference(nnf_transformation,[],[f30])).
% 42.89/5.98  
% 42.89/5.98  fof(f32,plain,(
% 42.89/5.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.89/5.98    inference(flattening,[],[f31])).
% 42.89/5.98  
% 42.89/5.98  fof(f34,plain,(
% 42.89/5.98    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 42.89/5.98    introduced(choice_axiom,[])).
% 42.89/5.98  
% 42.89/5.98  fof(f33,plain,(
% 42.89/5.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 42.89/5.98    introduced(choice_axiom,[])).
% 42.89/5.98  
% 42.89/5.98  fof(f35,plain,(
% 42.89/5.98    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 42.89/5.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 42.89/5.98  
% 42.89/5.98  fof(f52,plain,(
% 42.89/5.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 42.89/5.98    inference(cnf_transformation,[],[f35])).
% 42.89/5.98  
% 42.89/5.98  fof(f13,axiom,(
% 42.89/5.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 42.89/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.98  
% 42.89/5.98  fof(f28,plain,(
% 42.89/5.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.89/5.98    inference(ennf_transformation,[],[f13])).
% 42.89/5.98  
% 42.89/5.98  fof(f49,plain,(
% 42.89/5.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.89/5.98    inference(cnf_transformation,[],[f28])).
% 42.89/5.98  
% 42.89/5.98  fof(f8,axiom,(
% 42.89/5.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 42.89/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.98  
% 42.89/5.98  fof(f20,plain,(
% 42.89/5.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.89/5.98    inference(ennf_transformation,[],[f8])).
% 42.89/5.98  
% 42.89/5.98  fof(f43,plain,(
% 42.89/5.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.89/5.98    inference(cnf_transformation,[],[f20])).
% 42.89/5.98  
% 42.89/5.98  fof(f51,plain,(
% 42.89/5.98    l1_pre_topc(sK0)),
% 42.89/5.98    inference(cnf_transformation,[],[f35])).
% 42.89/5.98  
% 42.89/5.98  fof(f53,plain,(
% 42.89/5.98    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 42.89/5.98    inference(cnf_transformation,[],[f35])).
% 42.89/5.98  
% 42.89/5.98  fof(f12,axiom,(
% 42.89/5.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 42.89/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.98  
% 42.89/5.98  fof(f26,plain,(
% 42.89/5.98    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.89/5.98    inference(ennf_transformation,[],[f12])).
% 42.89/5.98  
% 42.89/5.98  fof(f27,plain,(
% 42.89/5.98    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.89/5.98    inference(flattening,[],[f26])).
% 42.89/5.98  
% 42.89/5.98  fof(f48,plain,(
% 42.89/5.98    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.89/5.98    inference(cnf_transformation,[],[f27])).
% 42.89/5.98  
% 42.89/5.98  fof(f4,axiom,(
% 42.89/5.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 42.89/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.98  
% 42.89/5.98  fof(f17,plain,(
% 42.89/5.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 42.89/5.98    inference(ennf_transformation,[],[f4])).
% 42.89/5.98  
% 42.89/5.98  fof(f39,plain,(
% 42.89/5.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 42.89/5.98    inference(cnf_transformation,[],[f17])).
% 42.89/5.98  
% 42.89/5.98  fof(f6,axiom,(
% 42.89/5.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 42.89/5.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.98  
% 42.89/5.98  fof(f41,plain,(
% 42.89/5.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 42.89/5.98    inference(cnf_transformation,[],[f6])).
% 42.89/5.98  
% 42.89/5.98  fof(f56,plain,(
% 42.89/5.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 42.89/5.99    inference(definition_unfolding,[],[f39,f41])).
% 42.89/5.99  
% 42.89/5.99  fof(f2,axiom,(
% 42.89/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 42.89/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.99  
% 42.89/5.99  fof(f37,plain,(
% 42.89/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 42.89/5.99    inference(cnf_transformation,[],[f2])).
% 42.89/5.99  
% 42.89/5.99  fof(f55,plain,(
% 42.89/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 42.89/5.99    inference(definition_unfolding,[],[f37,f41,f41])).
% 42.89/5.99  
% 42.89/5.99  fof(f5,axiom,(
% 42.89/5.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 42.89/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.99  
% 42.89/5.99  fof(f40,plain,(
% 42.89/5.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 42.89/5.99    inference(cnf_transformation,[],[f5])).
% 42.89/5.99  
% 42.89/5.99  fof(f3,axiom,(
% 42.89/5.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 42.89/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.99  
% 42.89/5.99  fof(f16,plain,(
% 42.89/5.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 42.89/5.99    inference(ennf_transformation,[],[f3])).
% 42.89/5.99  
% 42.89/5.99  fof(f38,plain,(
% 42.89/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 42.89/5.99    inference(cnf_transformation,[],[f16])).
% 42.89/5.99  
% 42.89/5.99  fof(f11,axiom,(
% 42.89/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 42.89/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.99  
% 42.89/5.99  fof(f25,plain,(
% 42.89/5.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.89/5.99    inference(ennf_transformation,[],[f11])).
% 42.89/5.99  
% 42.89/5.99  fof(f47,plain,(
% 42.89/5.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.89/5.99    inference(cnf_transformation,[],[f25])).
% 42.89/5.99  
% 42.89/5.99  fof(f10,axiom,(
% 42.89/5.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 42.89/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.99  
% 42.89/5.99  fof(f23,plain,(
% 42.89/5.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 42.89/5.99    inference(ennf_transformation,[],[f10])).
% 42.89/5.99  
% 42.89/5.99  fof(f24,plain,(
% 42.89/5.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 42.89/5.99    inference(flattening,[],[f23])).
% 42.89/5.99  
% 42.89/5.99  fof(f46,plain,(
% 42.89/5.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.89/5.99    inference(cnf_transformation,[],[f24])).
% 42.89/5.99  
% 42.89/5.99  fof(f7,axiom,(
% 42.89/5.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 42.89/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.99  
% 42.89/5.99  fof(f18,plain,(
% 42.89/5.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 42.89/5.99    inference(ennf_transformation,[],[f7])).
% 42.89/5.99  
% 42.89/5.99  fof(f19,plain,(
% 42.89/5.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.89/5.99    inference(flattening,[],[f18])).
% 42.89/5.99  
% 42.89/5.99  fof(f42,plain,(
% 42.89/5.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.89/5.99    inference(cnf_transformation,[],[f19])).
% 42.89/5.99  
% 42.89/5.99  fof(f54,plain,(
% 42.89/5.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 42.89/5.99    inference(cnf_transformation,[],[f35])).
% 42.89/5.99  
% 42.89/5.99  fof(f9,axiom,(
% 42.89/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 42.89/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.89/5.99  
% 42.89/5.99  fof(f21,plain,(
% 42.89/5.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.89/5.99    inference(ennf_transformation,[],[f9])).
% 42.89/5.99  
% 42.89/5.99  fof(f22,plain,(
% 42.89/5.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.89/5.99    inference(flattening,[],[f21])).
% 42.89/5.99  
% 42.89/5.99  fof(f45,plain,(
% 42.89/5.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.89/5.99    inference(cnf_transformation,[],[f22])).
% 42.89/5.99  
% 42.89/5.99  fof(f50,plain,(
% 42.89/5.99    v2_pre_topc(sK0)),
% 42.89/5.99    inference(cnf_transformation,[],[f35])).
% 42.89/5.99  
% 42.89/5.99  cnf(c_0,plain,
% 42.89/5.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 42.89/5.99      inference(cnf_transformation,[],[f36]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_15,negated_conjecture,
% 42.89/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 42.89/5.99      inference(cnf_transformation,[],[f52]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_618,plain,
% 42.89/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_12,plain,
% 42.89/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.89/5.99      | ~ l1_pre_topc(X1)
% 42.89/5.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 42.89/5.99      inference(cnf_transformation,[],[f49]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_621,plain,
% 42.89/5.99      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 42.89/5.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 42.89/5.99      | l1_pre_topc(X0) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_3646,plain,
% 42.89/5.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 42.89/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_618,c_621]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_6,plain,
% 42.89/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.89/5.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 42.89/5.99      inference(cnf_transformation,[],[f43]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_627,plain,
% 42.89/5.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 42.89/5.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_1899,plain,
% 42.89/5.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_618,c_627]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_3649,plain,
% 42.89/5.99      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 42.89/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 42.89/5.99      inference(demodulation,[status(thm)],[c_3646,c_1899]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_16,negated_conjecture,
% 42.89/5.99      ( l1_pre_topc(sK0) ),
% 42.89/5.99      inference(cnf_transformation,[],[f51]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_19,plain,
% 42.89/5.99      ( l1_pre_topc(sK0) = iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4053,plain,
% 42.89/5.99      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 42.89/5.99      inference(global_propositional_subsumption,
% 42.89/5.99                [status(thm)],
% 42.89/5.99                [c_3649,c_19]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_14,negated_conjecture,
% 42.89/5.99      ( v4_pre_topc(sK1,sK0)
% 42.89/5.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.89/5.99      inference(cnf_transformation,[],[f53]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_619,plain,
% 42.89/5.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.89/5.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_11,plain,
% 42.89/5.99      ( ~ v4_pre_topc(X0,X1)
% 42.89/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.89/5.99      | r1_tarski(k2_tops_1(X1,X0),X0)
% 42.89/5.99      | ~ l1_pre_topc(X1) ),
% 42.89/5.99      inference(cnf_transformation,[],[f48]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_622,plain,
% 42.89/5.99      ( v4_pre_topc(X0,X1) != iProver_top
% 42.89/5.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 42.89/5.99      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 42.89/5.99      | l1_pre_topc(X1) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_1037,plain,
% 42.89/5.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 42.89/5.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 42.89/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_618,c_622]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_1282,plain,
% 42.89/5.99      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 42.89/5.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.89/5.99      inference(global_propositional_subsumption,
% 42.89/5.99                [status(thm)],
% 42.89/5.99                [c_1037,c_19]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_1283,plain,
% 42.89/5.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 42.89/5.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 42.89/5.99      inference(renaming,[status(thm)],[c_1282]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_3,plain,
% 42.89/5.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 42.89/5.99      inference(cnf_transformation,[],[f56]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_630,plain,
% 42.89/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 42.89/5.99      | r1_tarski(X0,X1) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_1288,plain,
% 42.89/5.99      ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
% 42.89/5.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_1283,c_630]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_1461,plain,
% 42.89/5.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.89/5.99      | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_619,c_1288]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_1,plain,
% 42.89/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 42.89/5.99      inference(cnf_transformation,[],[f55]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_1473,plain,
% 42.89/5.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.89/5.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_1461,c_1]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4058,plain,
% 42.89/5.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.89/5.99      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.89/5.99      inference(demodulation,[status(thm)],[c_4053,c_1473]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4061,plain,
% 42.89/5.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.89/5.99      inference(demodulation,[status(thm)],[c_4058,c_1899]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4,plain,
% 42.89/5.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 42.89/5.99      inference(cnf_transformation,[],[f40]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_629,plain,
% 42.89/5.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4135,plain,
% 42.89/5.99      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_4061,c_629]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_2,plain,
% 42.89/5.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 42.89/5.99      inference(cnf_transformation,[],[f38]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_631,plain,
% 42.89/5.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_6826,plain,
% 42.89/5.99      ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_4135,c_631]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_121858,plain,
% 42.89/5.99      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_0,c_6826]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_10,plain,
% 42.89/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.89/5.99      | ~ l1_pre_topc(X1)
% 42.89/5.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 42.89/5.99      inference(cnf_transformation,[],[f47]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_623,plain,
% 42.89/5.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 42.89/5.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 42.89/5.99      | l1_pre_topc(X0) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4868,plain,
% 42.89/5.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 42.89/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_618,c_623]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_9,plain,
% 42.89/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.89/5.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 42.89/5.99      | ~ l1_pre_topc(X1) ),
% 42.89/5.99      inference(cnf_transformation,[],[f46]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_624,plain,
% 42.89/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 42.89/5.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 42.89/5.99      | l1_pre_topc(X1) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_5,plain,
% 42.89/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.89/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 42.89/5.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 42.89/5.99      inference(cnf_transformation,[],[f42]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_628,plain,
% 42.89/5.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 42.89/5.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 42.89/5.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_3622,plain,
% 42.89/5.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 42.89/5.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_618,c_628]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_3884,plain,
% 42.89/5.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 42.89/5.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.89/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_624,c_3622]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4409,plain,
% 42.89/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.89/5.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 42.89/5.99      inference(global_propositional_subsumption,
% 42.89/5.99                [status(thm)],
% 42.89/5.99                [c_3884,c_19]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4410,plain,
% 42.89/5.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 42.89/5.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 42.89/5.99      inference(renaming,[status(thm)],[c_4409]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4418,plain,
% 42.89/5.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 42.89/5.99      inference(superposition,[status(thm)],[c_618,c_4410]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_4871,plain,
% 42.89/5.99      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 42.89/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 42.89/5.99      inference(demodulation,[status(thm)],[c_4868,c_4418]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_5371,plain,
% 42.89/5.99      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 42.89/5.99      inference(global_propositional_subsumption,
% 42.89/5.99                [status(thm)],
% 42.89/5.99                [c_4871,c_19]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_122257,plain,
% 42.89/5.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 42.89/5.99      inference(demodulation,[status(thm)],[c_121858,c_5371]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_13,negated_conjecture,
% 42.89/5.99      ( ~ v4_pre_topc(sK1,sK0)
% 42.89/5.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 42.89/5.99      inference(cnf_transformation,[],[f54]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_620,plain,
% 42.89/5.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 42.89/5.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_2438,plain,
% 42.89/5.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 42.89/5.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.89/5.99      inference(demodulation,[status(thm)],[c_1899,c_620]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_7,plain,
% 42.89/5.99      ( v4_pre_topc(X0,X1)
% 42.89/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.89/5.99      | ~ l1_pre_topc(X1)
% 42.89/5.99      | ~ v2_pre_topc(X1)
% 42.89/5.99      | k2_pre_topc(X1,X0) != X0 ),
% 42.89/5.99      inference(cnf_transformation,[],[f45]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_840,plain,
% 42.89/5.99      ( v4_pre_topc(sK1,sK0)
% 42.89/5.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 42.89/5.99      | ~ l1_pre_topc(sK0)
% 42.89/5.99      | ~ v2_pre_topc(sK0)
% 42.89/5.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 42.89/5.99      inference(instantiation,[status(thm)],[c_7]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_841,plain,
% 42.89/5.99      ( k2_pre_topc(sK0,sK1) != sK1
% 42.89/5.99      | v4_pre_topc(sK1,sK0) = iProver_top
% 42.89/5.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.89/5.99      | l1_pre_topc(sK0) != iProver_top
% 42.89/5.99      | v2_pre_topc(sK0) != iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_20,plain,
% 42.89/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_17,negated_conjecture,
% 42.89/5.99      ( v2_pre_topc(sK0) ),
% 42.89/5.99      inference(cnf_transformation,[],[f50]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(c_18,plain,
% 42.89/5.99      ( v2_pre_topc(sK0) = iProver_top ),
% 42.89/5.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 42.89/5.99  
% 42.89/5.99  cnf(contradiction,plain,
% 42.89/5.99      ( $false ),
% 42.89/5.99      inference(minisat,
% 42.89/5.99                [status(thm)],
% 42.89/5.99                [c_122257,c_4061,c_2438,c_841,c_20,c_19,c_18]) ).
% 42.89/5.99  
% 42.89/5.99  
% 42.89/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 42.89/5.99  
% 42.89/5.99  ------                               Statistics
% 42.89/5.99  
% 42.89/5.99  ------ Selected
% 42.89/5.99  
% 42.89/5.99  total_time:                             5.341
% 42.89/5.99  
%------------------------------------------------------------------------------

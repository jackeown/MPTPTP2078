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
% DateTime   : Thu Dec  3 12:14:48 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 714 expanded)
%              Number of clauses        :   74 ( 240 expanded)
%              Number of leaves         :   19 ( 158 expanded)
%              Depth                    :   19
%              Number of atoms          :  322 (2553 expanded)
%              Number of equality atoms :  158 ( 928 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_721,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_731,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5531,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_721,c_731])).

cnf(c_19,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_722,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5646,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5531,c_722])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_728,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6303,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_728])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7603,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6303,c_24])).

cnf(c_7604,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7603])).

cnf(c_7609,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5646,c_7604])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_736,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1772,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_736])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_737,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2483,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1772,c_737])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3394,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2483,c_4])).

cnf(c_3774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_3394,c_4])).

cnf(c_3786,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_3774,c_4])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_734,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_750,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_734,c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_735,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2620,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_750,c_735])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_730,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_733,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2505,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_730,c_733])).

cnf(c_2618,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_730,c_735])).

cnf(c_2626,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2618,c_3])).

cnf(c_3406,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2505,c_2626])).

cnf(c_3536,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2620,c_3406])).

cnf(c_5008,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3786,c_3536])).

cnf(c_7832,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7609,c_5008])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_727,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k4_xboole_0(X2,X0)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_732,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11832,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k4_xboole_0(X0,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_732])).

cnf(c_14093,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_11832])).

cnf(c_14557,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14093,c_24])).

cnf(c_14558,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_14557])).

cnf(c_14567,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_721,c_14558])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_724,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1198,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_724])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1546,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1198,c_21,c_20,c_1020])).

cnf(c_14572,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_14567,c_1546])).

cnf(c_14586,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_7832,c_14572])).

cnf(c_3539,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3536,c_2483])).

cnf(c_14607,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_14586,c_3539])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_725,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2294,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_725])).

cnf(c_1027,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3190,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2294,c_21,c_20,c_1027])).

cnf(c_23851,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_14607,c_3190])).

cnf(c_12,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1013,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_18,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23851,c_14607,c_1013,c_18,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:48:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.81/1.46  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.46  
% 7.81/1.46  ------  iProver source info
% 7.81/1.46  
% 7.81/1.46  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.46  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.46  git: non_committed_changes: false
% 7.81/1.46  git: last_make_outside_of_git: false
% 7.81/1.46  
% 7.81/1.46  ------ 
% 7.81/1.46  ------ Parsing...
% 7.81/1.46  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.46  ------ Proving...
% 7.81/1.46  ------ Problem Properties 
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  clauses                                 23
% 7.81/1.46  conjectures                             5
% 7.81/1.46  EPR                                     2
% 7.81/1.46  Horn                                    22
% 7.81/1.46  unary                                   10
% 7.81/1.46  binary                                  6
% 7.81/1.46  lits                                    47
% 7.81/1.46  lits eq                                 15
% 7.81/1.46  fd_pure                                 0
% 7.81/1.46  fd_pseudo                               0
% 7.81/1.46  fd_cond                                 0
% 7.81/1.46  fd_pseudo_cond                          0
% 7.81/1.46  AC symbols                              0
% 7.81/1.46  
% 7.81/1.46  ------ Input Options Time Limit: Unbounded
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  ------ 
% 7.81/1.46  Current options:
% 7.81/1.46  ------ 
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  ------ Proving...
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  % SZS status Theorem for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  fof(f20,conjecture,(
% 7.81/1.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f21,negated_conjecture,(
% 7.81/1.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.81/1.46    inference(negated_conjecture,[],[f20])).
% 7.81/1.46  
% 7.81/1.46  fof(f37,plain,(
% 7.81/1.46    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.81/1.46    inference(ennf_transformation,[],[f21])).
% 7.81/1.46  
% 7.81/1.46  fof(f38,plain,(
% 7.81/1.46    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.46    inference(flattening,[],[f37])).
% 7.81/1.46  
% 7.81/1.46  fof(f39,plain,(
% 7.81/1.46    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.46    inference(nnf_transformation,[],[f38])).
% 7.81/1.46  
% 7.81/1.46  fof(f40,plain,(
% 7.81/1.46    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.46    inference(flattening,[],[f39])).
% 7.81/1.46  
% 7.81/1.46  fof(f42,plain,(
% 7.81/1.46    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f41,plain,(
% 7.81/1.46    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f43,plain,(
% 7.81/1.46    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.81/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 7.81/1.46  
% 7.81/1.46  fof(f65,plain,(
% 7.81/1.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.81/1.46    inference(cnf_transformation,[],[f43])).
% 7.81/1.46  
% 7.81/1.46  fof(f12,axiom,(
% 7.81/1.46    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f28,plain,(
% 7.81/1.46    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.46    inference(ennf_transformation,[],[f12])).
% 7.81/1.46  
% 7.81/1.46  fof(f55,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f28])).
% 7.81/1.46  
% 7.81/1.46  fof(f66,plain,(
% 7.81/1.46    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.81/1.46    inference(cnf_transformation,[],[f43])).
% 7.81/1.46  
% 7.81/1.46  fof(f15,axiom,(
% 7.81/1.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f29,plain,(
% 7.81/1.46    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.46    inference(ennf_transformation,[],[f15])).
% 7.81/1.46  
% 7.81/1.46  fof(f30,plain,(
% 7.81/1.46    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.46    inference(flattening,[],[f29])).
% 7.81/1.46  
% 7.81/1.46  fof(f57,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f30])).
% 7.81/1.46  
% 7.81/1.46  fof(f64,plain,(
% 7.81/1.46    l1_pre_topc(sK0)),
% 7.81/1.46    inference(cnf_transformation,[],[f43])).
% 7.81/1.46  
% 7.81/1.46  fof(f4,axiom,(
% 7.81/1.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f47,plain,(
% 7.81/1.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.81/1.46    inference(cnf_transformation,[],[f4])).
% 7.81/1.46  
% 7.81/1.46  fof(f3,axiom,(
% 7.81/1.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f46,plain,(
% 7.81/1.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f3])).
% 7.81/1.46  
% 7.81/1.46  fof(f1,axiom,(
% 7.81/1.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f23,plain,(
% 7.81/1.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.81/1.46    inference(ennf_transformation,[],[f1])).
% 7.81/1.46  
% 7.81/1.46  fof(f44,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f23])).
% 7.81/1.46  
% 7.81/1.46  fof(f6,axiom,(
% 7.81/1.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f49,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f6])).
% 7.81/1.46  
% 7.81/1.46  fof(f68,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.81/1.46    inference(definition_unfolding,[],[f44,f49])).
% 7.81/1.46  
% 7.81/1.46  fof(f5,axiom,(
% 7.81/1.46    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f48,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f5])).
% 7.81/1.46  
% 7.81/1.46  fof(f70,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 7.81/1.46    inference(definition_unfolding,[],[f48,f49])).
% 7.81/1.46  
% 7.81/1.46  fof(f9,axiom,(
% 7.81/1.46    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f52,plain,(
% 7.81/1.46    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f9])).
% 7.81/1.46  
% 7.81/1.46  fof(f7,axiom,(
% 7.81/1.46    ! [X0] : k2_subset_1(X0) = X0),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f50,plain,(
% 7.81/1.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.81/1.46    inference(cnf_transformation,[],[f7])).
% 7.81/1.46  
% 7.81/1.46  fof(f8,axiom,(
% 7.81/1.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f24,plain,(
% 7.81/1.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.46    inference(ennf_transformation,[],[f8])).
% 7.81/1.46  
% 7.81/1.46  fof(f51,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f24])).
% 7.81/1.46  
% 7.81/1.46  fof(f13,axiom,(
% 7.81/1.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f56,plain,(
% 7.81/1.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f13])).
% 7.81/1.46  
% 7.81/1.46  fof(f10,axiom,(
% 7.81/1.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f25,plain,(
% 7.81/1.46    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.46    inference(ennf_transformation,[],[f10])).
% 7.81/1.46  
% 7.81/1.46  fof(f53,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f25])).
% 7.81/1.46  
% 7.81/1.46  fof(f16,axiom,(
% 7.81/1.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f31,plain,(
% 7.81/1.46    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.81/1.46    inference(ennf_transformation,[],[f16])).
% 7.81/1.46  
% 7.81/1.46  fof(f32,plain,(
% 7.81/1.46    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.81/1.46    inference(flattening,[],[f31])).
% 7.81/1.46  
% 7.81/1.46  fof(f59,plain,(
% 7.81/1.46    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f32])).
% 7.81/1.46  
% 7.81/1.46  fof(f11,axiom,(
% 7.81/1.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f26,plain,(
% 7.81/1.46    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.81/1.46    inference(ennf_transformation,[],[f11])).
% 7.81/1.46  
% 7.81/1.46  fof(f27,plain,(
% 7.81/1.46    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.46    inference(flattening,[],[f26])).
% 7.81/1.46  
% 7.81/1.46  fof(f54,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f27])).
% 7.81/1.46  
% 7.81/1.46  fof(f71,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(definition_unfolding,[],[f54,f49])).
% 7.81/1.46  
% 7.81/1.46  fof(f19,axiom,(
% 7.81/1.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f36,plain,(
% 7.81/1.46    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.46    inference(ennf_transformation,[],[f19])).
% 7.81/1.46  
% 7.81/1.46  fof(f62,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f36])).
% 7.81/1.46  
% 7.81/1.46  fof(f18,axiom,(
% 7.81/1.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.81/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f35,plain,(
% 7.81/1.46    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.46    inference(ennf_transformation,[],[f18])).
% 7.81/1.46  
% 7.81/1.46  fof(f61,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f35])).
% 7.81/1.46  
% 7.81/1.46  fof(f58,plain,(
% 7.81/1.46    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f30])).
% 7.81/1.46  
% 7.81/1.46  fof(f67,plain,(
% 7.81/1.46    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.81/1.46    inference(cnf_transformation,[],[f43])).
% 7.81/1.46  
% 7.81/1.46  fof(f63,plain,(
% 7.81/1.46    v2_pre_topc(sK0)),
% 7.81/1.46    inference(cnf_transformation,[],[f43])).
% 7.81/1.46  
% 7.81/1.46  cnf(c_20,negated_conjecture,
% 7.81/1.46      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.81/1.46      inference(cnf_transformation,[],[f65]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_721,plain,
% 7.81/1.46      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_10,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.46      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.81/1.46      inference(cnf_transformation,[],[f55]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_731,plain,
% 7.81/1.46      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 7.81/1.46      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5531,plain,
% 7.81/1.46      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_721,c_731]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_19,negated_conjecture,
% 7.81/1.46      ( v4_pre_topc(sK1,sK0)
% 7.81/1.46      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.46      inference(cnf_transformation,[],[f66]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_722,plain,
% 7.81/1.46      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.81/1.46      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5646,plain,
% 7.81/1.46      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.81/1.46      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_5531,c_722]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_13,plain,
% 7.81/1.46      ( ~ v4_pre_topc(X0,X1)
% 7.81/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.46      | ~ l1_pre_topc(X1)
% 7.81/1.46      | k2_pre_topc(X1,X0) = X0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f57]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_728,plain,
% 7.81/1.46      ( k2_pre_topc(X0,X1) = X1
% 7.81/1.46      | v4_pre_topc(X1,X0) != iProver_top
% 7.81/1.46      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.81/1.46      | l1_pre_topc(X0) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_6303,plain,
% 7.81/1.46      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.46      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.81/1.46      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_721,c_728]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_21,negated_conjecture,
% 7.81/1.46      ( l1_pre_topc(sK0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f64]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_24,plain,
% 7.81/1.46      ( l1_pre_topc(sK0) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_7603,plain,
% 7.81/1.46      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.81/1.46      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.81/1.46      inference(global_propositional_subsumption,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_6303,c_24]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_7604,plain,
% 7.81/1.46      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.46      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.81/1.46      inference(renaming,[status(thm)],[c_7603]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_7609,plain,
% 7.81/1.46      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.46      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_5646,c_7604]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3,plain,
% 7.81/1.46      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f47]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2,plain,
% 7.81/1.46      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f46]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_736,plain,
% 7.81/1.46      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1772,plain,
% 7.81/1.46      ( r1_tarski(X0,X0) = iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_3,c_736]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_0,plain,
% 7.81/1.46      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 7.81/1.46      inference(cnf_transformation,[],[f68]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_737,plain,
% 7.81/1.46      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
% 7.81/1.46      | r1_tarski(X0,X1) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2483,plain,
% 7.81/1.46      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_1772,c_737]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_4,plain,
% 7.81/1.46      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.46      inference(cnf_transformation,[],[f70]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3394,plain,
% 7.81/1.46      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_2483,c_4]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3774,plain,
% 7.81/1.46      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_3394,c_4]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3786,plain,
% 7.81/1.46      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_3774,c_4]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_7,plain,
% 7.81/1.46      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.81/1.46      inference(cnf_transformation,[],[f52]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_734,plain,
% 7.81/1.46      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5,plain,
% 7.81/1.46      ( k2_subset_1(X0) = X0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f50]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_750,plain,
% 7.81/1.46      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_734,c_5]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_6,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.46      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f51]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_735,plain,
% 7.81/1.46      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.81/1.46      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2620,plain,
% 7.81/1.46      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_750,c_735]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_11,plain,
% 7.81/1.46      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.81/1.46      inference(cnf_transformation,[],[f56]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_730,plain,
% 7.81/1.46      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_8,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.46      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f53]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_733,plain,
% 7.81/1.46      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.81/1.46      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2505,plain,
% 7.81/1.46      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_730,c_733]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2618,plain,
% 7.81/1.46      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_730,c_735]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2626,plain,
% 7.81/1.46      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_2618,c_3]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3406,plain,
% 7.81/1.46      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_2505,c_2626]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3536,plain,
% 7.81/1.46      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_2620,c_3406]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5008,plain,
% 7.81/1.46      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_3786,c_3536]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_7832,plain,
% 7.81/1.46      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.46      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_7609,c_5008]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.46      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.46      | ~ l1_pre_topc(X1) ),
% 7.81/1.46      inference(cnf_transformation,[],[f59]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_727,plain,
% 7.81/1.46      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.81/1.46      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.81/1.46      | l1_pre_topc(X1) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_9,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.46      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.81/1.46      | k5_xboole_0(X0,k4_xboole_0(X2,X0)) = k4_subset_1(X1,X0,X2) ),
% 7.81/1.46      inference(cnf_transformation,[],[f71]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_732,plain,
% 7.81/1.46      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 7.81/1.46      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.81/1.46      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_11832,plain,
% 7.81/1.46      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k4_xboole_0(X0,sK1))
% 7.81/1.46      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_721,c_732]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14093,plain,
% 7.81/1.46      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
% 7.81/1.46      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.81/1.46      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_727,c_11832]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14557,plain,
% 7.81/1.46      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.81/1.46      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1)) ),
% 7.81/1.46      inference(global_propositional_subsumption,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_14093,c_24]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14558,plain,
% 7.81/1.46      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
% 7.81/1.46      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.81/1.46      inference(renaming,[status(thm)],[c_14557]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14567,plain,
% 7.81/1.46      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_721,c_14558]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_17,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.46      | ~ l1_pre_topc(X1)
% 7.81/1.46      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f62]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_724,plain,
% 7.81/1.46      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.81/1.46      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.81/1.46      | l1_pre_topc(X0) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1198,plain,
% 7.81/1.46      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.81/1.46      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_721,c_724]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1020,plain,
% 7.81/1.46      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.81/1.46      | ~ l1_pre_topc(sK0)
% 7.81/1.46      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_17]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1546,plain,
% 7.81/1.46      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.81/1.46      inference(global_propositional_subsumption,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_1198,c_21,c_20,c_1020]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14572,plain,
% 7.81/1.46      ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_14567,c_1546]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14586,plain,
% 7.81/1.46      ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
% 7.81/1.46      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_7832,c_14572]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3539,plain,
% 7.81/1.46      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_3536,c_2483]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14607,plain,
% 7.81/1.46      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_14586,c_3539]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_16,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.46      | ~ l1_pre_topc(X1)
% 7.81/1.46      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f61]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_725,plain,
% 7.81/1.46      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.81/1.46      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.81/1.46      | l1_pre_topc(X0) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2294,plain,
% 7.81/1.46      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.81/1.46      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_721,c_725]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1027,plain,
% 7.81/1.46      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.81/1.46      | ~ l1_pre_topc(sK0)
% 7.81/1.46      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_16]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3190,plain,
% 7.81/1.46      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.46      inference(global_propositional_subsumption,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_2294,c_21,c_20,c_1027]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_23851,plain,
% 7.81/1.46      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_14607,c_3190]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_12,plain,
% 7.81/1.46      ( v4_pre_topc(X0,X1)
% 7.81/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.46      | ~ l1_pre_topc(X1)
% 7.81/1.46      | ~ v2_pre_topc(X1)
% 7.81/1.46      | k2_pre_topc(X1,X0) != X0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f58]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1013,plain,
% 7.81/1.46      ( v4_pre_topc(sK1,sK0)
% 7.81/1.46      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.81/1.46      | ~ l1_pre_topc(sK0)
% 7.81/1.46      | ~ v2_pre_topc(sK0)
% 7.81/1.46      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_12]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_18,negated_conjecture,
% 7.81/1.46      ( ~ v4_pre_topc(sK1,sK0)
% 7.81/1.46      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.81/1.46      inference(cnf_transformation,[],[f67]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22,negated_conjecture,
% 7.81/1.46      ( v2_pre_topc(sK0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f63]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(contradiction,plain,
% 7.81/1.46      ( $false ),
% 7.81/1.46      inference(minisat,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_23851,c_14607,c_1013,c_18,c_20,c_21,c_22]) ).
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  ------                               Statistics
% 7.81/1.46  
% 7.81/1.46  ------ Selected
% 7.81/1.46  
% 7.81/1.46  total_time:                             0.639
% 7.81/1.46  
%------------------------------------------------------------------------------

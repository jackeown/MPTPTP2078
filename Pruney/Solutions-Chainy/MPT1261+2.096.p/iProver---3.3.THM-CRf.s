%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:38 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 431 expanded)
%              Number of clauses        :   67 ( 120 expanded)
%              Number of leaves         :   16 (  95 expanded)
%              Depth                    :   19
%              Number of atoms          :  310 (1984 expanded)
%              Number of equality atoms :  147 ( 630 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f52,plain,
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

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f55,plain,(
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

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f41,f41])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_592,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_599,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_601,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4986,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_592,c_601])).

cnf(c_5385,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_4986])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5385,c_18])).

cnf(c_5682,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5681])).

cnf(c_5690,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_592,c_5682])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_597,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3229,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_592,c_597])).

cnf(c_804,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3667,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3229,c_15,c_14,c_804])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_600,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2367,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_592,c_600])).

cnf(c_13,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_593,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2370,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2367,c_593])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_596,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1872,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_592,c_596])).

cnf(c_2683,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1872,c_18])).

cnf(c_2684,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2683])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_604,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2690,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2684,c_604])).

cnf(c_2996,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2370,c_2690])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_602,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1120,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_602,c_604])).

cnf(c_3200,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2996,c_1120])).

cnf(c_4368,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_3200])).

cnf(c_5692,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5690,c_3667,c_4368])).

cnf(c_8,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_598,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4818,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_592,c_598])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_750,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_751,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_5534,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4818,c_17,c_18,c_19,c_751])).

cnf(c_5851,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5692,c_5534])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_603,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2689,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2684,c_603])).

cnf(c_3000,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2370,c_2689])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3701,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3000,c_1])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_595,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1000,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_592,c_595])).

cnf(c_807,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1272,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_15,c_14,c_807])).

cnf(c_2382,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1272,c_2367])).

cnf(c_3704,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3701,c_2382])).

cnf(c_12,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_594,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2371,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2367,c_594])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5851,c_3704,c_2371])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:53:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 3.65/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.99  
% 3.65/0.99  ------  iProver source info
% 3.65/0.99  
% 3.65/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.99  git: non_committed_changes: false
% 3.65/0.99  git: last_make_outside_of_git: false
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  ------ Parsing...
% 3.65/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.99  ------ Proving...
% 3.65/0.99  ------ Problem Properties 
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  clauses                                 17
% 3.65/0.99  conjectures                             5
% 3.65/0.99  EPR                                     2
% 3.65/0.99  Horn                                    16
% 3.65/0.99  unary                                   6
% 3.65/0.99  binary                                  5
% 3.65/0.99  lits                                    36
% 3.65/0.99  lits eq                                 10
% 3.65/0.99  fd_pure                                 0
% 3.65/0.99  fd_pseudo                               0
% 3.65/0.99  fd_cond                                 0
% 3.65/0.99  fd_pseudo_cond                          0
% 3.65/0.99  AC symbols                              0
% 3.65/0.99  
% 3.65/0.99  ------ Input Options Time Limit: Unbounded
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  Current options:
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ Proving...
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS status Theorem for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  fof(f14,conjecture,(
% 3.65/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f15,negated_conjecture,(
% 3.65/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.65/0.99    inference(negated_conjecture,[],[f14])).
% 3.65/0.99  
% 3.65/0.99  fof(f29,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f15])).
% 3.65/0.99  
% 3.65/0.99  fof(f30,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.65/0.99    inference(flattening,[],[f29])).
% 3.65/0.99  
% 3.65/0.99  fof(f31,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.65/0.99    inference(nnf_transformation,[],[f30])).
% 3.65/0.99  
% 3.65/0.99  fof(f32,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.65/0.99    inference(flattening,[],[f31])).
% 3.65/0.99  
% 3.65/0.99  fof(f34,plain,(
% 3.65/0.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f33,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f35,plain,(
% 3.65/0.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 3.65/0.99  
% 3.65/0.99  fof(f51,plain,(
% 3.65/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.65/0.99    inference(cnf_transformation,[],[f35])).
% 3.65/0.99  
% 3.65/0.99  fof(f9,axiom,(
% 3.65/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f21,plain,(
% 3.65/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f9])).
% 3.65/0.99  
% 3.65/0.99  fof(f22,plain,(
% 3.65/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(flattening,[],[f21])).
% 3.65/0.99  
% 3.65/0.99  fof(f44,plain,(
% 3.65/0.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f22])).
% 3.65/0.99  
% 3.65/0.99  fof(f7,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f18,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.65/0.99    inference(ennf_transformation,[],[f7])).
% 3.65/0.99  
% 3.65/0.99  fof(f19,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/0.99    inference(flattening,[],[f18])).
% 3.65/0.99  
% 3.65/0.99  fof(f42,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f19])).
% 3.65/0.99  
% 3.65/0.99  fof(f50,plain,(
% 3.65/0.99    l1_pre_topc(sK0)),
% 3.65/0.99    inference(cnf_transformation,[],[f35])).
% 3.65/0.99  
% 3.65/0.99  fof(f11,axiom,(
% 3.65/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f25,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f11])).
% 3.65/0.99  
% 3.65/0.99  fof(f46,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f25])).
% 3.65/0.99  
% 3.65/0.99  fof(f1,axiom,(
% 3.65/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f36,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f1])).
% 3.65/0.99  
% 3.65/0.99  fof(f8,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f20,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f8])).
% 3.65/0.99  
% 3.65/0.99  fof(f43,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f20])).
% 3.65/0.99  
% 3.65/0.99  fof(f52,plain,(
% 3.65/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.65/0.99    inference(cnf_transformation,[],[f35])).
% 3.65/0.99  
% 3.65/0.99  fof(f12,axiom,(
% 3.65/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f26,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f12])).
% 3.65/0.99  
% 3.65/0.99  fof(f27,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.99    inference(flattening,[],[f26])).
% 3.65/0.99  
% 3.65/0.99  fof(f47,plain,(
% 3.65/0.99    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f27])).
% 3.65/0.99  
% 3.65/0.99  fof(f3,axiom,(
% 3.65/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f16,plain,(
% 3.65/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.65/0.99    inference(ennf_transformation,[],[f3])).
% 3.65/0.99  
% 3.65/0.99  fof(f38,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f16])).
% 3.65/0.99  
% 3.65/0.99  fof(f5,axiom,(
% 3.65/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f40,plain,(
% 3.65/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f5])).
% 3.65/0.99  
% 3.65/0.99  fof(f10,axiom,(
% 3.65/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f23,plain,(
% 3.65/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f10])).
% 3.65/0.99  
% 3.65/0.99  fof(f24,plain,(
% 3.65/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.65/0.99    inference(flattening,[],[f23])).
% 3.65/0.99  
% 3.65/0.99  fof(f45,plain,(
% 3.65/0.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f24])).
% 3.65/0.99  
% 3.65/0.99  fof(f49,plain,(
% 3.65/0.99    v2_pre_topc(sK0)),
% 3.65/0.99    inference(cnf_transformation,[],[f35])).
% 3.65/0.99  
% 3.65/0.99  fof(f4,axiom,(
% 3.65/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f17,plain,(
% 3.65/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.65/0.99    inference(ennf_transformation,[],[f4])).
% 3.65/0.99  
% 3.65/0.99  fof(f39,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f17])).
% 3.65/0.99  
% 3.65/0.99  fof(f6,axiom,(
% 3.65/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f41,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f6])).
% 3.65/0.99  
% 3.65/0.99  fof(f55,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.65/0.99    inference(definition_unfolding,[],[f39,f41])).
% 3.65/0.99  
% 3.65/0.99  fof(f2,axiom,(
% 3.65/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f37,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f2])).
% 3.65/0.99  
% 3.65/0.99  fof(f54,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.65/0.99    inference(definition_unfolding,[],[f37,f41,f41])).
% 3.65/0.99  
% 3.65/0.99  fof(f13,axiom,(
% 3.65/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f28,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f13])).
% 3.65/1.00  
% 3.65/1.00  fof(f48,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  fof(f53,plain,(
% 3.65/1.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.65/1.00    inference(cnf_transformation,[],[f35])).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14,negated_conjecture,
% 3.65/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_592,plain,
% 3.65/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/1.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/1.00      | ~ l1_pre_topc(X1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_599,plain,
% 3.65/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.65/1.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.65/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.65/1.00      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_601,plain,
% 3.65/1.00      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4986,plain,
% 3.65/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_592,c_601]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5385,plain,
% 3.65/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.65/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_599,c_4986]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_15,negated_conjecture,
% 3.65/1.00      ( l1_pre_topc(sK0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_18,plain,
% 3.65/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5681,plain,
% 3.65/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.65/1.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_5385,c_18]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5682,plain,
% 3.65/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_5681]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5690,plain,
% 3.65/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_592,c_5682]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/1.00      | ~ l1_pre_topc(X1)
% 3.65/1.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_597,plain,
% 3.65/1.00      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3229,plain,
% 3.65/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.65/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_592,c_597]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_804,plain,
% 3.65/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.65/1.00      | ~ l1_pre_topc(sK0)
% 3.65/1.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3667,plain,
% 3.65/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_3229,c_15,c_14,c_804]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_0,plain,
% 3.65/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/1.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.65/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_600,plain,
% 3.65/1.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2367,plain,
% 3.65/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_592,c_600]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13,negated_conjecture,
% 3.65/1.00      ( v4_pre_topc(sK1,sK0)
% 3.65/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_593,plain,
% 3.65/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.65/1.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2370,plain,
% 3.65/1.00      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.65/1.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_2367,c_593]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_10,plain,
% 3.65/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/1.00      | r1_tarski(k2_tops_1(X1,X0),X0)
% 3.65/1.00      | ~ l1_pre_topc(X1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_596,plain,
% 3.65/1.00      ( v4_pre_topc(X0,X1) != iProver_top
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.65/1.00      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.65/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1872,plain,
% 3.65/1.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.65/1.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.65/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_592,c_596]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2683,plain,
% 3.65/1.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.65/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_1872,c_18]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2684,plain,
% 3.65/1.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.65/1.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_2683]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2,plain,
% 3.65/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.65/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_604,plain,
% 3.65/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2690,plain,
% 3.65/1.00      ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1
% 3.65/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_2684,c_604]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2996,plain,
% 3.65/1.00      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.65/1.00      | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_2370,c_2690]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4,plain,
% 3.65/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_602,plain,
% 3.65/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1120,plain,
% 3.65/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_602,c_604]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3200,plain,
% 3.65/1.00      ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_2996,c_1120]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4368,plain,
% 3.65/1.00      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_0,c_3200]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5692,plain,
% 3.65/1.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_5690,c_3667,c_4368]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8,plain,
% 3.65/1.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/1.00      | ~ v2_pre_topc(X0)
% 3.65/1.00      | ~ l1_pre_topc(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_598,plain,
% 3.65/1.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/1.00      | v2_pre_topc(X0) != iProver_top
% 3.65/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4818,plain,
% 3.65/1.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.65/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.65/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_592,c_598]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_16,negated_conjecture,
% 3.65/1.00      ( v2_pre_topc(sK0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17,plain,
% 3.65/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_19,plain,
% 3.65/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_750,plain,
% 3.65/1.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 3.65/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.65/1.00      | ~ v2_pre_topc(sK0)
% 3.65/1.00      | ~ l1_pre_topc(sK0) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_751,plain,
% 3.65/1.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.65/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.65/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.65/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5534,plain,
% 3.65/1.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_4818,c_17,c_18,c_19,c_751]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5851,plain,
% 3.65/1.00      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_5692,c_5534]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3,plain,
% 3.65/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_603,plain,
% 3.65/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.65/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2689,plain,
% 3.65/1.00      ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
% 3.65/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_2684,c_603]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3000,plain,
% 3.65/1.00      ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
% 3.65/1.00      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_2370,c_2689]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1,plain,
% 3.65/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3701,plain,
% 3.65/1.00      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.65/1.00      | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_3000,c_1]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/1.00      | ~ l1_pre_topc(X1)
% 3.65/1.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_595,plain,
% 3.65/1.00      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1000,plain,
% 3.65/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.65/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_592,c_595]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_807,plain,
% 3.65/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.65/1.00      | ~ l1_pre_topc(sK0)
% 3.65/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1272,plain,
% 3.65/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_1000,c_15,c_14,c_807]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2382,plain,
% 3.65/1.00      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1272,c_2367]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3704,plain,
% 3.65/1.00      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_3701,c_2382]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_12,negated_conjecture,
% 3.65/1.00      ( ~ v4_pre_topc(sK1,sK0)
% 3.65/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_594,plain,
% 3.65/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.65/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2371,plain,
% 3.65/1.00      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.65/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_2367,c_594]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(contradiction,plain,
% 3.65/1.00      ( $false ),
% 3.65/1.00      inference(minisat,[status(thm)],[c_5851,c_3704,c_2371]) ).
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  ------                               Statistics
% 3.65/1.00  
% 3.65/1.00  ------ Selected
% 3.65/1.00  
% 3.65/1.00  total_time:                             0.265
% 3.65/1.00  
%------------------------------------------------------------------------------

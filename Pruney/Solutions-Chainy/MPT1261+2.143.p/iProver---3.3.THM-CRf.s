%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:45 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 492 expanded)
%              Number of clauses        :   53 ( 128 expanded)
%              Number of leaves         :   15 ( 112 expanded)
%              Depth                    :   17
%              Number of atoms          :  283 (2261 expanded)
%              Number of equality atoms :  132 ( 734 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

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
    inference(flattening,[],[f30])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f34,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f52,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_605,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_614,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1211,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_605,c_614])).

cnf(c_13,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_606,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1214,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1211,c_606])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_612,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4736,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_612])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4897,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4736,c_18])).

cnf(c_4898,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4897])).

cnf(c_4903,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1214,c_4898])).

cnf(c_3,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_616,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_617,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1093,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_616,c_617])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_892,plain,
    ( k3_tarski(k2_tarski(X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_1430,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_1093,c_892])).

cnf(c_5258,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_4903,c_1430])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_615,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4710,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X2)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_615])).

cnf(c_14828,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_4710])).

cnf(c_15390,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14828,c_18])).

cnf(c_15391,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15390])).

cnf(c_15399,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_605,c_15391])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_608,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_987,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_608])).

cnf(c_810,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1300,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_987,c_15,c_14,c_810])).

cnf(c_15401,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_15399,c_1300])).

cnf(c_15413,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_5258,c_15401])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_609,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1718,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_609])).

cnf(c_848,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2175,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1718,c_15,c_14,c_848])).

cnf(c_18800,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_15413,c_2175])).

cnf(c_6,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_807,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_12,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18800,c_15413,c_807,c_12,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:48:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.51/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/1.50  
% 7.51/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.51/1.50  
% 7.51/1.50  ------  iProver source info
% 7.51/1.50  
% 7.51/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.51/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.51/1.50  git: non_committed_changes: false
% 7.51/1.50  git: last_make_outside_of_git: false
% 7.51/1.50  
% 7.51/1.50  ------ 
% 7.51/1.50  ------ Parsing...
% 7.51/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.51/1.50  
% 7.51/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.51/1.50  
% 7.51/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.51/1.50  
% 7.51/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.50  ------ Proving...
% 7.51/1.50  ------ Problem Properties 
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  clauses                                 17
% 7.51/1.50  conjectures                             5
% 7.51/1.50  EPR                                     2
% 7.51/1.50  Horn                                    16
% 7.51/1.50  unary                                   6
% 7.51/1.50  binary                                  4
% 7.51/1.50  lits                                    39
% 7.51/1.50  lits eq                                 11
% 7.51/1.50  fd_pure                                 0
% 7.51/1.50  fd_pseudo                               0
% 7.51/1.50  fd_cond                                 0
% 7.51/1.50  fd_pseudo_cond                          0
% 7.51/1.50  AC symbols                              0
% 7.51/1.50  
% 7.51/1.50  ------ Input Options Time Limit: Unbounded
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  ------ 
% 7.51/1.50  Current options:
% 7.51/1.50  ------ 
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  ------ Proving...
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  % SZS status Theorem for theBenchmark.p
% 7.51/1.50  
% 7.51/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.51/1.50  
% 7.51/1.50  fof(f14,conjecture,(
% 7.51/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f15,negated_conjecture,(
% 7.51/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.51/1.50    inference(negated_conjecture,[],[f14])).
% 7.51/1.50  
% 7.51/1.50  fof(f28,plain,(
% 7.51/1.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.51/1.50    inference(ennf_transformation,[],[f15])).
% 7.51/1.50  
% 7.51/1.50  fof(f29,plain,(
% 7.51/1.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.51/1.50    inference(flattening,[],[f28])).
% 7.51/1.50  
% 7.51/1.50  fof(f30,plain,(
% 7.51/1.50    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.51/1.50    inference(nnf_transformation,[],[f29])).
% 7.51/1.50  
% 7.51/1.50  fof(f31,plain,(
% 7.51/1.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.51/1.50    inference(flattening,[],[f30])).
% 7.51/1.50  
% 7.51/1.50  fof(f33,plain,(
% 7.51/1.50    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.51/1.50    introduced(choice_axiom,[])).
% 7.51/1.50  
% 7.51/1.50  fof(f32,plain,(
% 7.51/1.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.51/1.50    introduced(choice_axiom,[])).
% 7.51/1.50  
% 7.51/1.50  fof(f34,plain,(
% 7.51/1.50    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.51/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 7.51/1.50  
% 7.51/1.50  fof(f51,plain,(
% 7.51/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.51/1.50    inference(cnf_transformation,[],[f34])).
% 7.51/1.50  
% 7.51/1.50  fof(f8,axiom,(
% 7.51/1.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f19,plain,(
% 7.51/1.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.51/1.50    inference(ennf_transformation,[],[f8])).
% 7.51/1.50  
% 7.51/1.50  fof(f42,plain,(
% 7.51/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.51/1.50    inference(cnf_transformation,[],[f19])).
% 7.51/1.50  
% 7.51/1.50  fof(f2,axiom,(
% 7.51/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f36,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.51/1.50    inference(cnf_transformation,[],[f2])).
% 7.51/1.50  
% 7.51/1.50  fof(f57,plain,(
% 7.51/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.51/1.50    inference(definition_unfolding,[],[f42,f36])).
% 7.51/1.50  
% 7.51/1.50  fof(f52,plain,(
% 7.51/1.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.51/1.50    inference(cnf_transformation,[],[f34])).
% 7.51/1.50  
% 7.51/1.50  fof(f9,axiom,(
% 7.51/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f20,plain,(
% 7.51/1.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.51/1.50    inference(ennf_transformation,[],[f9])).
% 7.51/1.50  
% 7.51/1.50  fof(f21,plain,(
% 7.51/1.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.51/1.50    inference(flattening,[],[f20])).
% 7.51/1.50  
% 7.51/1.50  fof(f43,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f21])).
% 7.51/1.50  
% 7.51/1.50  fof(f50,plain,(
% 7.51/1.50    l1_pre_topc(sK0)),
% 7.51/1.50    inference(cnf_transformation,[],[f34])).
% 7.51/1.50  
% 7.51/1.50  fof(f5,axiom,(
% 7.51/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f39,plain,(
% 7.51/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f5])).
% 7.51/1.50  
% 7.51/1.50  fof(f55,plain,(
% 7.51/1.50    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.51/1.50    inference(definition_unfolding,[],[f39,f36])).
% 7.51/1.50  
% 7.51/1.50  fof(f4,axiom,(
% 7.51/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f16,plain,(
% 7.51/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.51/1.50    inference(ennf_transformation,[],[f4])).
% 7.51/1.50  
% 7.51/1.50  fof(f38,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f16])).
% 7.51/1.50  
% 7.51/1.50  fof(f1,axiom,(
% 7.51/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f35,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f1])).
% 7.51/1.50  
% 7.51/1.50  fof(f3,axiom,(
% 7.51/1.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f37,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.51/1.50    inference(cnf_transformation,[],[f3])).
% 7.51/1.50  
% 7.51/1.50  fof(f6,axiom,(
% 7.51/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f40,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.51/1.50    inference(cnf_transformation,[],[f6])).
% 7.51/1.50  
% 7.51/1.50  fof(f54,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0) )),
% 7.51/1.50    inference(definition_unfolding,[],[f37,f40])).
% 7.51/1.50  
% 7.51/1.50  fof(f10,axiom,(
% 7.51/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f22,plain,(
% 7.51/1.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.51/1.50    inference(ennf_transformation,[],[f10])).
% 7.51/1.50  
% 7.51/1.50  fof(f23,plain,(
% 7.51/1.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.51/1.50    inference(flattening,[],[f22])).
% 7.51/1.50  
% 7.51/1.50  fof(f45,plain,(
% 7.51/1.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f23])).
% 7.51/1.50  
% 7.51/1.50  fof(f7,axiom,(
% 7.51/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f17,plain,(
% 7.51/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.51/1.50    inference(ennf_transformation,[],[f7])).
% 7.51/1.50  
% 7.51/1.50  fof(f18,plain,(
% 7.51/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.51/1.50    inference(flattening,[],[f17])).
% 7.51/1.50  
% 7.51/1.50  fof(f41,plain,(
% 7.51/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.51/1.50    inference(cnf_transformation,[],[f18])).
% 7.51/1.50  
% 7.51/1.50  fof(f56,plain,(
% 7.51/1.50    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.51/1.50    inference(definition_unfolding,[],[f41,f40])).
% 7.51/1.50  
% 7.51/1.50  fof(f13,axiom,(
% 7.51/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f27,plain,(
% 7.51/1.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.51/1.50    inference(ennf_transformation,[],[f13])).
% 7.51/1.50  
% 7.51/1.50  fof(f48,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f27])).
% 7.51/1.50  
% 7.51/1.50  fof(f12,axiom,(
% 7.51/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.51/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.51/1.50  
% 7.51/1.50  fof(f26,plain,(
% 7.51/1.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.51/1.50    inference(ennf_transformation,[],[f12])).
% 7.51/1.50  
% 7.51/1.50  fof(f47,plain,(
% 7.51/1.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f26])).
% 7.51/1.50  
% 7.51/1.50  fof(f44,plain,(
% 7.51/1.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.51/1.50    inference(cnf_transformation,[],[f21])).
% 7.51/1.50  
% 7.51/1.50  fof(f53,plain,(
% 7.51/1.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.51/1.50    inference(cnf_transformation,[],[f34])).
% 7.51/1.50  
% 7.51/1.50  fof(f49,plain,(
% 7.51/1.50    v2_pre_topc(sK0)),
% 7.51/1.50    inference(cnf_transformation,[],[f34])).
% 7.51/1.50  
% 7.51/1.50  cnf(c_14,negated_conjecture,
% 7.51/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.51/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_605,plain,
% 7.51/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.51/1.50      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.51/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_614,plain,
% 7.51/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 7.51/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1211,plain,
% 7.51/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_605,c_614]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_13,negated_conjecture,
% 7.51/1.50      ( v4_pre_topc(sK1,sK0)
% 7.51/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_606,plain,
% 7.51/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.51/1.50      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1214,plain,
% 7.51/1.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 7.51/1.50      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.51/1.50      inference(demodulation,[status(thm)],[c_1211,c_606]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_7,plain,
% 7.51/1.50      ( ~ v4_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | k2_pre_topc(X1,X0) = X0 ),
% 7.51/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_612,plain,
% 7.51/1.50      ( k2_pre_topc(X0,X1) = X1
% 7.51/1.50      | v4_pre_topc(X1,X0) != iProver_top
% 7.51/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.51/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4736,plain,
% 7.51/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.51/1.50      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_605,c_612]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15,negated_conjecture,
% 7.51/1.50      ( l1_pre_topc(sK0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_18,plain,
% 7.51/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4897,plain,
% 7.51/1.50      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.51/1.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_4736,c_18]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4898,plain,
% 7.51/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.51/1.50      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_4897]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4903,plain,
% 7.51/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.51/1.50      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1214,c_4898]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_3,plain,
% 7.51/1.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_616,plain,
% 7.51/1.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2,plain,
% 7.51/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.51/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_617,plain,
% 7.51/1.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1093,plain,
% 7.51/1.50      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_616,c_617]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_0,plain,
% 7.51/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1,plain,
% 7.51/1.50      ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
% 7.51/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_892,plain,
% 7.51/1.50      ( k3_tarski(k2_tarski(X0,k3_xboole_0(X1,X0))) = X0 ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1430,plain,
% 7.51/1.50      ( k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_1093,c_892]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_5258,plain,
% 7.51/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.51/1.50      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_4903,c_1430]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_8,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | ~ l1_pre_topc(X1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_611,plain,
% 7.51/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.51/1.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.51/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.51/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.51/1.50      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 7.51/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_615,plain,
% 7.51/1.50      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 7.51/1.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.51/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_4710,plain,
% 7.51/1.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X2)))
% 7.51/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.51/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.51/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_611,c_615]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_14828,plain,
% 7.51/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 7.51/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_605,c_4710]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15390,plain,
% 7.51/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.51/1.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_14828,c_18]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15391,plain,
% 7.51/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 7.51/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.51/1.50      inference(renaming,[status(thm)],[c_15390]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15399,plain,
% 7.51/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_605,c_15391]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_11,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_608,plain,
% 7.51/1.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.51/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.51/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_987,plain,
% 7.51/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_605,c_608]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_810,plain,
% 7.51/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.51/1.50      | ~ l1_pre_topc(sK0)
% 7.51/1.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1300,plain,
% 7.51/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_987,c_15,c_14,c_810]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15401,plain,
% 7.51/1.50      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 7.51/1.50      inference(light_normalisation,[status(thm)],[c_15399,c_1300]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_15413,plain,
% 7.51/1.50      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_5258,c_15401]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_10,plain,
% 7.51/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_609,plain,
% 7.51/1.50      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.51/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.51/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.51/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_1718,plain,
% 7.51/1.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.51/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.51/1.50      inference(superposition,[status(thm)],[c_605,c_609]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_848,plain,
% 7.51/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.51/1.50      | ~ l1_pre_topc(sK0)
% 7.51/1.50      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_2175,plain,
% 7.51/1.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.51/1.50      inference(global_propositional_subsumption,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_1718,c_15,c_14,c_848]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_18800,plain,
% 7.51/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.51/1.50      inference(demodulation,[status(thm)],[c_15413,c_2175]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_6,plain,
% 7.51/1.50      ( v4_pre_topc(X0,X1)
% 7.51/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.51/1.50      | ~ l1_pre_topc(X1)
% 7.51/1.50      | ~ v2_pre_topc(X1)
% 7.51/1.50      | k2_pre_topc(X1,X0) != X0 ),
% 7.51/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_807,plain,
% 7.51/1.50      ( v4_pre_topc(sK1,sK0)
% 7.51/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.51/1.50      | ~ l1_pre_topc(sK0)
% 7.51/1.50      | ~ v2_pre_topc(sK0)
% 7.51/1.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.51/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_12,negated_conjecture,
% 7.51/1.50      ( ~ v4_pre_topc(sK1,sK0)
% 7.51/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.51/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(c_16,negated_conjecture,
% 7.51/1.50      ( v2_pre_topc(sK0) ),
% 7.51/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.51/1.50  
% 7.51/1.50  cnf(contradiction,plain,
% 7.51/1.50      ( $false ),
% 7.51/1.50      inference(minisat,
% 7.51/1.50                [status(thm)],
% 7.51/1.50                [c_18800,c_15413,c_807,c_12,c_14,c_15,c_16]) ).
% 7.51/1.50  
% 7.51/1.50  
% 7.51/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.51/1.50  
% 7.51/1.50  ------                               Statistics
% 7.51/1.50  
% 7.51/1.50  ------ Selected
% 7.51/1.50  
% 7.51/1.50  total_time:                             0.677
% 7.51/1.50  
%------------------------------------------------------------------------------

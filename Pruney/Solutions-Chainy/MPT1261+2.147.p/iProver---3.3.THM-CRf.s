%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:45 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 716 expanded)
%              Number of clauses        :   66 ( 196 expanded)
%              Number of leaves         :   17 ( 178 expanded)
%              Depth                    :   18
%              Number of atoms          :  296 (2479 expanded)
%              Number of equality atoms :  148 ( 958 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

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
    inference(flattening,[],[f32])).

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f36,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f45,f45])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_677,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_685,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8677,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_677,c_685])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_678,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9150,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8677,c_678])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_683,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9130,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_683])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9607,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9130,c_23])).

cnf(c_9608,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9607])).

cnf(c_9684,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_9150,c_9608])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_708,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1,c_11])).

cnf(c_1248,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11,c_708])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_705,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7,c_11])).

cnf(c_1265,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1248,c_705])).

cnf(c_1363,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_708,c_1265])).

cnf(c_1378,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1363,c_708])).

cnf(c_4786,plain,
    ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_1378,c_705])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_687,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_950,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_687])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_690,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2038,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_950,c_690])).

cnf(c_4796,plain,
    ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4786,c_2038])).

cnf(c_4921,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1265,c_4796])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5019,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4921,c_6])).

cnf(c_5032,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5019,c_4])).

cnf(c_10675,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_9684,c_5032])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_682,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_686,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8858,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_686])).

cnf(c_9424,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_682,c_8858])).

cnf(c_9937,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9424,c_23])).

cnf(c_9938,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9937])).

cnf(c_9946,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_677,c_9938])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_680,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1761,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_680])).

cnf(c_942,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2172,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1761,c_20,c_19,c_942])).

cnf(c_9948,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_9946,c_2172])).

cnf(c_10746,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_10675,c_9948])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_681,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10080,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_681])).

cnf(c_945,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_10454,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10080,c_20,c_19,c_945])).

cnf(c_10969,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10746,c_10454])).

cnf(c_12,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_939,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10969,c_10746,c_939,c_17,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:58:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.82/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/0.98  
% 3.82/0.98  ------  iProver source info
% 3.82/0.98  
% 3.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/0.98  git: non_committed_changes: false
% 3.82/0.98  git: last_make_outside_of_git: false
% 3.82/0.98  
% 3.82/0.98  ------ 
% 3.82/0.98  ------ Parsing...
% 3.82/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.98  ------ Proving...
% 3.82/0.98  ------ Problem Properties 
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  clauses                                 22
% 3.82/0.98  conjectures                             5
% 3.82/0.98  EPR                                     2
% 3.82/0.98  Horn                                    21
% 3.82/0.98  unary                                   10
% 3.82/0.98  binary                                  6
% 3.82/0.98  lits                                    43
% 3.82/0.98  lits eq                                 17
% 3.82/0.98  fd_pure                                 0
% 3.82/0.98  fd_pseudo                               0
% 3.82/0.98  fd_cond                                 0
% 3.82/0.98  fd_pseudo_cond                          0
% 3.82/0.98  AC symbols                              0
% 3.82/0.98  
% 3.82/0.98  ------ Input Options Time Limit: Unbounded
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  ------ 
% 3.82/0.98  Current options:
% 3.82/0.98  ------ 
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  ------ Proving...
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  % SZS status Theorem for theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  fof(f17,conjecture,(
% 3.82/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f18,negated_conjecture,(
% 3.82/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.82/0.98    inference(negated_conjecture,[],[f17])).
% 3.82/0.98  
% 3.82/0.98  fof(f29,plain,(
% 3.82/0.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.82/0.98    inference(ennf_transformation,[],[f18])).
% 3.82/0.98  
% 3.82/0.98  fof(f30,plain,(
% 3.82/0.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.82/0.98    inference(flattening,[],[f29])).
% 3.82/0.98  
% 3.82/0.98  fof(f32,plain,(
% 3.82/0.98    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.82/0.98    inference(nnf_transformation,[],[f30])).
% 3.82/0.98  
% 3.82/0.98  fof(f33,plain,(
% 3.82/0.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.82/0.98    inference(flattening,[],[f32])).
% 3.82/0.98  
% 3.82/0.98  fof(f35,plain,(
% 3.82/0.98    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.82/0.98    introduced(choice_axiom,[])).
% 3.82/0.98  
% 3.82/0.98  fof(f34,plain,(
% 3.82/0.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.82/0.98    introduced(choice_axiom,[])).
% 3.82/0.98  
% 3.82/0.98  fof(f36,plain,(
% 3.82/0.98    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.82/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 3.82/0.98  
% 3.82/0.98  fof(f57,plain,(
% 3.82/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.82/0.98    inference(cnf_transformation,[],[f36])).
% 3.82/0.98  
% 3.82/0.98  fof(f11,axiom,(
% 3.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f22,plain,(
% 3.82/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.82/0.98    inference(ennf_transformation,[],[f11])).
% 3.82/0.98  
% 3.82/0.98  fof(f48,plain,(
% 3.82/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.82/0.98    inference(cnf_transformation,[],[f22])).
% 3.82/0.98  
% 3.82/0.98  fof(f58,plain,(
% 3.82/0.98    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.82/0.98    inference(cnf_transformation,[],[f36])).
% 3.82/0.98  
% 3.82/0.98  fof(f13,axiom,(
% 3.82/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f23,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.82/0.98    inference(ennf_transformation,[],[f13])).
% 3.82/0.98  
% 3.82/0.98  fof(f24,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.82/0.98    inference(flattening,[],[f23])).
% 3.82/0.98  
% 3.82/0.98  fof(f50,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f24])).
% 3.82/0.98  
% 3.82/0.98  fof(f56,plain,(
% 3.82/0.98    l1_pre_topc(sK0)),
% 3.82/0.98    inference(cnf_transformation,[],[f36])).
% 3.82/0.98  
% 3.82/0.98  fof(f12,axiom,(
% 3.82/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f49,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.82/0.98    inference(cnf_transformation,[],[f12])).
% 3.82/0.98  
% 3.82/0.98  fof(f8,axiom,(
% 3.82/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f45,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.82/0.98    inference(cnf_transformation,[],[f8])).
% 3.82/0.98  
% 3.82/0.98  fof(f64,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.82/0.98    inference(definition_unfolding,[],[f49,f45])).
% 3.82/0.98  
% 3.82/0.98  fof(f1,axiom,(
% 3.82/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f37,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f1])).
% 3.82/0.98  
% 3.82/0.98  fof(f61,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.82/0.98    inference(definition_unfolding,[],[f37,f45,f45])).
% 3.82/0.98  
% 3.82/0.98  fof(f7,axiom,(
% 3.82/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f44,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.82/0.98    inference(cnf_transformation,[],[f7])).
% 3.82/0.98  
% 3.82/0.98  fof(f63,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.82/0.98    inference(definition_unfolding,[],[f44,f45])).
% 3.82/0.98  
% 3.82/0.98  fof(f4,axiom,(
% 3.82/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f41,plain,(
% 3.82/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.82/0.98    inference(cnf_transformation,[],[f4])).
% 3.82/0.98  
% 3.82/0.98  fof(f9,axiom,(
% 3.82/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f46,plain,(
% 3.82/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.82/0.98    inference(cnf_transformation,[],[f9])).
% 3.82/0.98  
% 3.82/0.98  fof(f2,axiom,(
% 3.82/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f31,plain,(
% 3.82/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.82/0.98    inference(nnf_transformation,[],[f2])).
% 3.82/0.98  
% 3.82/0.98  fof(f39,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f31])).
% 3.82/0.98  
% 3.82/0.98  fof(f6,axiom,(
% 3.82/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f43,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.82/0.98    inference(cnf_transformation,[],[f6])).
% 3.82/0.98  
% 3.82/0.98  fof(f14,axiom,(
% 3.82/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f25,plain,(
% 3.82/0.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.82/0.98    inference(ennf_transformation,[],[f14])).
% 3.82/0.98  
% 3.82/0.98  fof(f26,plain,(
% 3.82/0.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.82/0.98    inference(flattening,[],[f25])).
% 3.82/0.98  
% 3.82/0.98  fof(f52,plain,(
% 3.82/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f26])).
% 3.82/0.98  
% 3.82/0.98  fof(f10,axiom,(
% 3.82/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f20,plain,(
% 3.82/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.82/0.98    inference(ennf_transformation,[],[f10])).
% 3.82/0.98  
% 3.82/0.98  fof(f21,plain,(
% 3.82/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.82/0.98    inference(flattening,[],[f20])).
% 3.82/0.98  
% 3.82/0.98  fof(f47,plain,(
% 3.82/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.82/0.98    inference(cnf_transformation,[],[f21])).
% 3.82/0.98  
% 3.82/0.98  fof(f16,axiom,(
% 3.82/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f28,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.82/0.98    inference(ennf_transformation,[],[f16])).
% 3.82/0.98  
% 3.82/0.98  fof(f54,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f28])).
% 3.82/0.98  
% 3.82/0.98  fof(f15,axiom,(
% 3.82/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f27,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.82/0.98    inference(ennf_transformation,[],[f15])).
% 3.82/0.98  
% 3.82/0.98  fof(f53,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f27])).
% 3.82/0.98  
% 3.82/0.98  fof(f51,plain,(
% 3.82/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f24])).
% 3.82/0.98  
% 3.82/0.98  fof(f59,plain,(
% 3.82/0.98    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.82/0.98    inference(cnf_transformation,[],[f36])).
% 3.82/0.98  
% 3.82/0.98  fof(f55,plain,(
% 3.82/0.98    v2_pre_topc(sK0)),
% 3.82/0.98    inference(cnf_transformation,[],[f36])).
% 3.82/0.98  
% 3.82/0.98  cnf(c_19,negated_conjecture,
% 3.82/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.82/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_677,plain,
% 3.82/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10,plain,
% 3.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.82/0.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.82/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_685,plain,
% 3.82/0.98      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.82/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_8677,plain,
% 3.82/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_677,c_685]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_18,negated_conjecture,
% 3.82/0.98      ( v4_pre_topc(sK1,sK0)
% 3.82/0.98      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.82/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_678,plain,
% 3.82/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.82/0.98      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9150,plain,
% 3.82/0.98      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.82/0.98      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_8677,c_678]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_13,plain,
% 3.82/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.98      | ~ l1_pre_topc(X1)
% 3.82/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_683,plain,
% 3.82/0.98      ( k2_pre_topc(X0,X1) = X1
% 3.82/0.98      | v4_pre_topc(X1,X0) != iProver_top
% 3.82/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.82/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9130,plain,
% 3.82/0.98      ( k2_pre_topc(sK0,sK1) = sK1
% 3.82/0.98      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.82/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_677,c_683]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_20,negated_conjecture,
% 3.82/0.98      ( l1_pre_topc(sK0) ),
% 3.82/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_23,plain,
% 3.82/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9607,plain,
% 3.82/0.98      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.82/0.98      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_9130,c_23]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9608,plain,
% 3.82/0.98      ( k2_pre_topc(sK0,sK1) = sK1
% 3.82/0.98      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.82/0.98      inference(renaming,[status(thm)],[c_9607]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9684,plain,
% 3.82/0.98      ( k2_pre_topc(sK0,sK1) = sK1
% 3.82/0.98      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_9150,c_9608]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_11,plain,
% 3.82/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.82/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1,plain,
% 3.82/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.82/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_708,plain,
% 3.82/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 3.82/0.98      inference(light_normalisation,[status(thm)],[c_1,c_11]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1248,plain,
% 3.82/0.98      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_11,c_708]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_7,plain,
% 3.82/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.82/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_705,plain,
% 3.82/0.98      ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.82/0.98      inference(light_normalisation,[status(thm)],[c_7,c_11]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1265,plain,
% 3.82/0.98      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 3.82/0.98      inference(light_normalisation,[status(thm)],[c_1248,c_705]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1363,plain,
% 3.82/0.98      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_708,c_1265]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1378,plain,
% 3.82/0.98      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_1363,c_708]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4786,plain,
% 3.82/0.98      ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_1378,c_705]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4,plain,
% 3.82/0.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_8,plain,
% 3.82/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.82/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_687,plain,
% 3.82/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_950,plain,
% 3.82/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_4,c_687]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2,plain,
% 3.82/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_690,plain,
% 3.82/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.82/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2038,plain,
% 3.82/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_950,c_690]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4796,plain,
% 3.82/0.98      ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) = k1_xboole_0 ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_4786,c_2038]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4921,plain,
% 3.82/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_1265,c_4796]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_6,plain,
% 3.82/0.98      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.82/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5019,plain,
% 3.82/0.98      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_4921,c_6]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5032,plain,
% 3.82/0.98      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.82/0.98      inference(light_normalisation,[status(thm)],[c_5019,c_4]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10675,plain,
% 3.82/0.98      ( k2_pre_topc(sK0,sK1) = sK1
% 3.82/0.98      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_9684,c_5032]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_14,plain,
% 3.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.98      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.98      | ~ l1_pre_topc(X1) ),
% 3.82/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_682,plain,
% 3.82/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.82/0.98      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.82/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9,plain,
% 3.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.82/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.82/0.98      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.82/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_686,plain,
% 3.82/0.98      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 3.82/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.82/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_8858,plain,
% 3.82/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 3.82/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_677,c_686]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9424,plain,
% 3.82/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 3.82/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.82/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_682,c_8858]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9937,plain,
% 3.82/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.82/0.98      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_9424,c_23]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9938,plain,
% 3.82/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 3.82/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.82/0.98      inference(renaming,[status(thm)],[c_9937]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9946,plain,
% 3.82/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_677,c_9938]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_16,plain,
% 3.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.98      | ~ l1_pre_topc(X1)
% 3.82/0.98      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.82/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_680,plain,
% 3.82/0.98      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.82/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.82/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1761,plain,
% 3.82/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.82/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_677,c_680]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_942,plain,
% 3.82/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.82/0.98      | ~ l1_pre_topc(sK0)
% 3.82/0.98      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2172,plain,
% 3.82/0.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_1761,c_20,c_19,c_942]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9948,plain,
% 3.82/0.98      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.82/0.98      inference(light_normalisation,[status(thm)],[c_9946,c_2172]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10746,plain,
% 3.82/0.98      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_10675,c_9948]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_15,plain,
% 3.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.98      | ~ l1_pre_topc(X1)
% 3.82/0.98      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.82/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_681,plain,
% 3.82/0.98      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.82/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.82/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10080,plain,
% 3.82/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.82/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_677,c_681]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_945,plain,
% 3.82/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.82/0.98      | ~ l1_pre_topc(sK0)
% 3.82/0.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10454,plain,
% 3.82/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_10080,c_20,c_19,c_945]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10969,plain,
% 3.82/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_10746,c_10454]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_12,plain,
% 3.82/0.98      ( v4_pre_topc(X0,X1)
% 3.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.98      | ~ l1_pre_topc(X1)
% 3.82/0.98      | ~ v2_pre_topc(X1)
% 3.82/0.98      | k2_pre_topc(X1,X0) != X0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_939,plain,
% 3.82/0.98      ( v4_pre_topc(sK1,sK0)
% 3.82/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.82/0.98      | ~ l1_pre_topc(sK0)
% 3.82/0.98      | ~ v2_pre_topc(sK0)
% 3.82/0.98      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_17,negated_conjecture,
% 3.82/0.98      ( ~ v4_pre_topc(sK1,sK0)
% 3.82/0.98      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.82/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_21,negated_conjecture,
% 3.82/0.98      ( v2_pre_topc(sK0) ),
% 3.82/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(contradiction,plain,
% 3.82/0.98      ( $false ),
% 3.82/0.98      inference(minisat,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_10969,c_10746,c_939,c_17,c_19,c_20,c_21]) ).
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  ------                               Statistics
% 3.82/0.98  
% 3.82/0.98  ------ Selected
% 3.82/0.98  
% 3.82/0.98  total_time:                             0.364
% 3.82/0.98  
%------------------------------------------------------------------------------

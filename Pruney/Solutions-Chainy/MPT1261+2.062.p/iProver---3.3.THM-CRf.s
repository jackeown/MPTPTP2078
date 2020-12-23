%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:33 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 680 expanded)
%              Number of clauses        :   67 ( 192 expanded)
%              Number of leaves         :   17 ( 164 expanded)
%              Depth                    :   18
%              Number of atoms          :  304 (2453 expanded)
%              Number of equality atoms :  154 ( 928 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_625,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_634,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3559,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_625,c_634])).

cnf(c_17,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_626,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3562,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3559,c_626])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_632,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6522,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_632])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6984,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6522,c_22])).

cnf(c_6985,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6984])).

cnf(c_6990,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3562,c_6985])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_636,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_637,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_659,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_637,c_9])).

cnf(c_1827,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_636,c_659])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_656,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_9])).

cnf(c_2457,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1827,c_656])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_650,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_1056,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_650,c_9])).

cnf(c_1065,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1056,c_5])).

cnf(c_1626,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1065,c_656])).

cnf(c_1642,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1626,c_650])).

cnf(c_2471,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2457,c_1642])).

cnf(c_7509,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6990,c_2471])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_635,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6726,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k5_xboole_0(X1,k4_xboole_0(k2_tops_1(X0,X2),X1))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_631,c_635])).

cnf(c_15860,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_6726])).

cnf(c_16711,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15860,c_22])).

cnf(c_16712,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_16711])).

cnf(c_16720,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_625,c_16712])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_628,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1052,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_628])).

cnf(c_869,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1318,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1052,c_19,c_18,c_869])).

cnf(c_16722,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_16720,c_1318])).

cnf(c_16734,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_7509,c_16722])).

cnf(c_1057,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_9])).

cnf(c_1062,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1057,c_650])).

cnf(c_1627,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1062,c_656])).

cnf(c_1636,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1627,c_5])).

cnf(c_16735,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_16734,c_1636])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_629,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1744,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_629])).

cnf(c_877,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2260,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1744,c_19,c_18,c_877])).

cnf(c_17614,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_16735,c_2260])).

cnf(c_10,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_866,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_16,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17614,c_16735,c_866,c_16,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.66/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/1.48  
% 7.66/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.48  
% 7.66/1.48  ------  iProver source info
% 7.66/1.48  
% 7.66/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.48  git: non_committed_changes: false
% 7.66/1.48  git: last_make_outside_of_git: false
% 7.66/1.48  
% 7.66/1.48  ------ 
% 7.66/1.48  ------ Parsing...
% 7.66/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.48  
% 7.66/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.66/1.48  
% 7.66/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.48  
% 7.66/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.48  ------ Proving...
% 7.66/1.48  ------ Problem Properties 
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  clauses                                 21
% 7.66/1.48  conjectures                             5
% 7.66/1.48  EPR                                     2
% 7.66/1.48  Horn                                    20
% 7.66/1.48  unary                                   10
% 7.66/1.48  binary                                  4
% 7.66/1.48  lits                                    43
% 7.66/1.48  lits eq                                 15
% 7.66/1.48  fd_pure                                 0
% 7.66/1.48  fd_pseudo                               0
% 7.66/1.48  fd_cond                                 0
% 7.66/1.48  fd_pseudo_cond                          0
% 7.66/1.48  AC symbols                              0
% 7.66/1.48  
% 7.66/1.48  ------ Input Options Time Limit: Unbounded
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  ------ 
% 7.66/1.48  Current options:
% 7.66/1.48  ------ 
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  ------ Proving...
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  % SZS status Theorem for theBenchmark.p
% 7.66/1.48  
% 7.66/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.48  
% 7.66/1.48  fof(f18,conjecture,(
% 7.66/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f19,negated_conjecture,(
% 7.66/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.66/1.48    inference(negated_conjecture,[],[f18])).
% 7.66/1.48  
% 7.66/1.48  fof(f33,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.66/1.48    inference(ennf_transformation,[],[f19])).
% 7.66/1.48  
% 7.66/1.48  fof(f34,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.66/1.48    inference(flattening,[],[f33])).
% 7.66/1.48  
% 7.66/1.48  fof(f35,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.66/1.48    inference(nnf_transformation,[],[f34])).
% 7.66/1.48  
% 7.66/1.48  fof(f36,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.66/1.48    inference(flattening,[],[f35])).
% 7.66/1.48  
% 7.66/1.48  fof(f38,plain,(
% 7.66/1.48    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.66/1.48    introduced(choice_axiom,[])).
% 7.66/1.48  
% 7.66/1.48  fof(f37,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.66/1.48    introduced(choice_axiom,[])).
% 7.66/1.48  
% 7.66/1.48  fof(f39,plain,(
% 7.66/1.48    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.66/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 7.66/1.48  
% 7.66/1.48  fof(f60,plain,(
% 7.66/1.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f11,axiom,(
% 7.66/1.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f24,plain,(
% 7.66/1.48    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.66/1.48    inference(ennf_transformation,[],[f11])).
% 7.66/1.48  
% 7.66/1.48  fof(f50,plain,(
% 7.66/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.66/1.48    inference(cnf_transformation,[],[f24])).
% 7.66/1.48  
% 7.66/1.48  fof(f61,plain,(
% 7.66/1.48    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f13,axiom,(
% 7.66/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f25,plain,(
% 7.66/1.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.48    inference(ennf_transformation,[],[f13])).
% 7.66/1.48  
% 7.66/1.48  fof(f26,plain,(
% 7.66/1.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.48    inference(flattening,[],[f25])).
% 7.66/1.48  
% 7.66/1.48  fof(f52,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f26])).
% 7.66/1.48  
% 7.66/1.48  fof(f59,plain,(
% 7.66/1.48    l1_pre_topc(sK0)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f5,axiom,(
% 7.66/1.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f44,plain,(
% 7.66/1.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f5])).
% 7.66/1.48  
% 7.66/1.48  fof(f3,axiom,(
% 7.66/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f21,plain,(
% 7.66/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.66/1.48    inference(ennf_transformation,[],[f3])).
% 7.66/1.48  
% 7.66/1.48  fof(f42,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f21])).
% 7.66/1.48  
% 7.66/1.48  fof(f7,axiom,(
% 7.66/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f46,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.66/1.48    inference(cnf_transformation,[],[f7])).
% 7.66/1.48  
% 7.66/1.48  fof(f65,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.66/1.48    inference(definition_unfolding,[],[f42,f46])).
% 7.66/1.48  
% 7.66/1.48  fof(f12,axiom,(
% 7.66/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f51,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.66/1.48    inference(cnf_transformation,[],[f12])).
% 7.66/1.48  
% 7.66/1.48  fof(f68,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.66/1.48    inference(definition_unfolding,[],[f51,f46])).
% 7.66/1.48  
% 7.66/1.48  fof(f2,axiom,(
% 7.66/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f41,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.66/1.48    inference(cnf_transformation,[],[f2])).
% 7.66/1.48  
% 7.66/1.48  fof(f63,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.66/1.48    inference(definition_unfolding,[],[f41,f46])).
% 7.66/1.48  
% 7.66/1.48  fof(f4,axiom,(
% 7.66/1.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f43,plain,(
% 7.66/1.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.66/1.48    inference(cnf_transformation,[],[f4])).
% 7.66/1.48  
% 7.66/1.48  fof(f66,plain,(
% 7.66/1.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.66/1.48    inference(definition_unfolding,[],[f43,f46])).
% 7.66/1.48  
% 7.66/1.48  fof(f6,axiom,(
% 7.66/1.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f45,plain,(
% 7.66/1.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.66/1.48    inference(cnf_transformation,[],[f6])).
% 7.66/1.48  
% 7.66/1.48  fof(f14,axiom,(
% 7.66/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f27,plain,(
% 7.66/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.66/1.48    inference(ennf_transformation,[],[f14])).
% 7.66/1.48  
% 7.66/1.48  fof(f28,plain,(
% 7.66/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.66/1.48    inference(flattening,[],[f27])).
% 7.66/1.48  
% 7.66/1.48  fof(f54,plain,(
% 7.66/1.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f28])).
% 7.66/1.48  
% 7.66/1.48  fof(f10,axiom,(
% 7.66/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f22,plain,(
% 7.66/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.66/1.48    inference(ennf_transformation,[],[f10])).
% 7.66/1.48  
% 7.66/1.48  fof(f23,plain,(
% 7.66/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.66/1.48    inference(flattening,[],[f22])).
% 7.66/1.48  
% 7.66/1.48  fof(f49,plain,(
% 7.66/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.66/1.48    inference(cnf_transformation,[],[f23])).
% 7.66/1.48  
% 7.66/1.48  fof(f8,axiom,(
% 7.66/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f47,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f8])).
% 7.66/1.48  
% 7.66/1.48  fof(f67,plain,(
% 7.66/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.66/1.48    inference(definition_unfolding,[],[f49,f47])).
% 7.66/1.48  
% 7.66/1.48  fof(f17,axiom,(
% 7.66/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f32,plain,(
% 7.66/1.48    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.48    inference(ennf_transformation,[],[f17])).
% 7.66/1.48  
% 7.66/1.48  fof(f57,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f32])).
% 7.66/1.48  
% 7.66/1.48  fof(f16,axiom,(
% 7.66/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.66/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f31,plain,(
% 7.66/1.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.48    inference(ennf_transformation,[],[f16])).
% 7.66/1.48  
% 7.66/1.48  fof(f56,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f31])).
% 7.66/1.48  
% 7.66/1.48  fof(f53,plain,(
% 7.66/1.48    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f26])).
% 7.66/1.48  
% 7.66/1.48  fof(f62,plain,(
% 7.66/1.48    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f58,plain,(
% 7.66/1.48    v2_pre_topc(sK0)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  cnf(c_18,negated_conjecture,
% 7.66/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.66/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_625,plain,
% 7.66/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_8,plain,
% 7.66/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.66/1.48      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.66/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_634,plain,
% 7.66/1.48      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 7.66/1.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_3559,plain,
% 7.66/1.48      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_625,c_634]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_17,negated_conjecture,
% 7.66/1.48      ( v4_pre_topc(sK1,sK0)
% 7.66/1.48      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.66/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_626,plain,
% 7.66/1.48      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.66/1.48      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_3562,plain,
% 7.66/1.48      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.66/1.48      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.66/1.48      inference(demodulation,[status(thm)],[c_3559,c_626]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_11,plain,
% 7.66/1.48      ( ~ v4_pre_topc(X0,X1)
% 7.66/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.48      | ~ l1_pre_topc(X1)
% 7.66/1.48      | k2_pre_topc(X1,X0) = X0 ),
% 7.66/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_632,plain,
% 7.66/1.48      ( k2_pre_topc(X0,X1) = X1
% 7.66/1.48      | v4_pre_topc(X1,X0) != iProver_top
% 7.66/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.66/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_6522,plain,
% 7.66/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.66/1.48      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.66/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_625,c_632]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_19,negated_conjecture,
% 7.66/1.48      ( l1_pre_topc(sK0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_22,plain,
% 7.66/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_6984,plain,
% 7.66/1.48      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.66/1.48      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.66/1.48      inference(global_propositional_subsumption,
% 7.66/1.48                [status(thm)],
% 7.66/1.48                [c_6522,c_22]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_6985,plain,
% 7.66/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.66/1.48      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.66/1.48      inference(renaming,[status(thm)],[c_6984]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_6990,plain,
% 7.66/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.66/1.48      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_3562,c_6985]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_4,plain,
% 7.66/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_636,plain,
% 7.66/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_2,plain,
% 7.66/1.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.66/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_637,plain,
% 7.66/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.66/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_9,plain,
% 7.66/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.66/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_659,plain,
% 7.66/1.48      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 7.66/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.66/1.48      inference(demodulation,[status(thm)],[c_637,c_9]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1827,plain,
% 7.66/1.48      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_636,c_659]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_0,plain,
% 7.66/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.66/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_656,plain,
% 7.66/1.48      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.66/1.48      inference(light_normalisation,[status(thm)],[c_0,c_9]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_2457,plain,
% 7.66/1.48      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_1827,c_656]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_3,plain,
% 7.66/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.66/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_5,plain,
% 7.66/1.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.66/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_650,plain,
% 7.66/1.48      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.66/1.48      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1056,plain,
% 7.66/1.48      ( k1_setfam_1(k2_tarski(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_650,c_9]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1065,plain,
% 7.66/1.48      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 7.66/1.48      inference(light_normalisation,[status(thm)],[c_1056,c_5]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1626,plain,
% 7.66/1.48      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_1065,c_656]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1642,plain,
% 7.66/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.66/1.48      inference(light_normalisation,[status(thm)],[c_1626,c_650]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_2471,plain,
% 7.66/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.66/1.48      inference(demodulation,[status(thm)],[c_2457,c_1642]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_7509,plain,
% 7.66/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.66/1.48      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_6990,c_2471]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_12,plain,
% 7.66/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.48      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.48      | ~ l1_pre_topc(X1) ),
% 7.66/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_631,plain,
% 7.66/1.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.66/1.48      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.66/1.48      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_7,plain,
% 7.66/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.66/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.66/1.48      | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_635,plain,
% 7.66/1.48      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 7.66/1.48      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 7.66/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_6726,plain,
% 7.66/1.48      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k5_xboole_0(X1,k4_xboole_0(k2_tops_1(X0,X2),X1))
% 7.66/1.48      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.66/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.66/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_631,c_635]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_15860,plain,
% 7.66/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
% 7.66/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.66/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_625,c_6726]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_16711,plain,
% 7.66/1.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.66/1.48      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1)) ),
% 7.66/1.48      inference(global_propositional_subsumption,
% 7.66/1.48                [status(thm)],
% 7.66/1.48                [c_15860,c_22]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_16712,plain,
% 7.66/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
% 7.66/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.66/1.48      inference(renaming,[status(thm)],[c_16711]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_16720,plain,
% 7.66/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_625,c_16712]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_15,plain,
% 7.66/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.48      | ~ l1_pre_topc(X1)
% 7.66/1.48      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_628,plain,
% 7.66/1.48      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.66/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.66/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1052,plain,
% 7.66/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.66/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_625,c_628]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_869,plain,
% 7.66/1.48      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.66/1.48      | ~ l1_pre_topc(sK0)
% 7.66/1.48      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.66/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1318,plain,
% 7.66/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.66/1.48      inference(global_propositional_subsumption,
% 7.66/1.48                [status(thm)],
% 7.66/1.48                [c_1052,c_19,c_18,c_869]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_16722,plain,
% 7.66/1.48      ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.66/1.48      inference(light_normalisation,[status(thm)],[c_16720,c_1318]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_16734,plain,
% 7.66/1.48      ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
% 7.66/1.48      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_7509,c_16722]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1057,plain,
% 7.66/1.48      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_5,c_9]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1062,plain,
% 7.66/1.48      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.66/1.48      inference(light_normalisation,[status(thm)],[c_1057,c_650]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1627,plain,
% 7.66/1.48      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_1062,c_656]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1636,plain,
% 7.66/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.66/1.48      inference(light_normalisation,[status(thm)],[c_1627,c_5]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_16735,plain,
% 7.66/1.48      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.66/1.48      inference(demodulation,[status(thm)],[c_16734,c_1636]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_14,plain,
% 7.66/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.48      | ~ l1_pre_topc(X1)
% 7.66/1.48      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_629,plain,
% 7.66/1.48      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.66/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.66/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1744,plain,
% 7.66/1.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.66/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_625,c_629]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_877,plain,
% 7.66/1.48      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.66/1.48      | ~ l1_pre_topc(sK0)
% 7.66/1.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.66/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_2260,plain,
% 7.66/1.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.66/1.48      inference(global_propositional_subsumption,
% 7.66/1.48                [status(thm)],
% 7.66/1.48                [c_1744,c_19,c_18,c_877]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_17614,plain,
% 7.66/1.48      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.66/1.48      inference(demodulation,[status(thm)],[c_16735,c_2260]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_10,plain,
% 7.66/1.48      ( v4_pre_topc(X0,X1)
% 7.66/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.48      | ~ l1_pre_topc(X1)
% 7.66/1.48      | ~ v2_pre_topc(X1)
% 7.66/1.48      | k2_pre_topc(X1,X0) != X0 ),
% 7.66/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_866,plain,
% 7.66/1.48      ( v4_pre_topc(sK1,sK0)
% 7.66/1.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.66/1.48      | ~ l1_pre_topc(sK0)
% 7.66/1.48      | ~ v2_pre_topc(sK0)
% 7.66/1.48      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.66/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_16,negated_conjecture,
% 7.66/1.48      ( ~ v4_pre_topc(sK1,sK0)
% 7.66/1.48      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.66/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_20,negated_conjecture,
% 7.66/1.48      ( v2_pre_topc(sK0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(contradiction,plain,
% 7.66/1.48      ( $false ),
% 7.66/1.48      inference(minisat,
% 7.66/1.48                [status(thm)],
% 7.66/1.48                [c_17614,c_16735,c_866,c_16,c_18,c_19,c_20]) ).
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.48  
% 7.66/1.48  ------                               Statistics
% 7.66/1.48  
% 7.66/1.48  ------ Selected
% 7.66/1.48  
% 7.66/1.48  total_time:                             0.556
% 7.66/1.48  
%------------------------------------------------------------------------------

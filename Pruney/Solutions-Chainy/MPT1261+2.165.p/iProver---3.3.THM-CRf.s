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
% DateTime   : Thu Dec  3 12:14:48 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 614 expanded)
%              Number of clauses        :   69 ( 177 expanded)
%              Number of leaves         :   16 ( 138 expanded)
%              Depth                    :   21
%              Number of atoms          :  326 (2599 expanded)
%              Number of equality atoms :  150 ( 872 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
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

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f38,f36,f36])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f37,f39])).

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

fof(f46,plain,(
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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f39])).

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

fof(f49,plain,(
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

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_822,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_827,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_822,c_2])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_820,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2001,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_827,c_820])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_819,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1999,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_819,c_820])).

cnf(c_3387,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_2001,c_1999])).

cnf(c_14,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_121,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_311,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_312,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_121,c_312])).

cnf(c_362,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_364,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_15])).

cnf(c_451,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_364])).

cnf(c_452,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_3578,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3387,c_452])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_818,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_975,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_819,c_818])).

cnf(c_2252,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1999,c_975])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2312,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2252,c_0])).

cnf(c_3418,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2001,c_2312])).

cnf(c_4740,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3578,c_3418])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4745,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_4740,c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_815,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_821,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2666,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_815,c_821])).

cnf(c_5087,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_819,c_2666])).

cnf(c_5279,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_819,c_5087])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_817,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_950,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_819,c_817])).

cnf(c_5289,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5279,c_950])).

cnf(c_5495,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4745,c_5289])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_816,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_1041,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_819,c_816])).

cnf(c_6052,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5495,c_1041])).

cnf(c_13,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_119,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_235,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_236,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_236,c_16])).

cnf(c_241,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_119,c_241])).

cnf(c_373,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_375,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6052,c_5495,c_375])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.34/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.02  
% 3.34/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/1.02  
% 3.34/1.02  ------  iProver source info
% 3.34/1.02  
% 3.34/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.34/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/1.02  git: non_committed_changes: false
% 3.34/1.02  git: last_make_outside_of_git: false
% 3.34/1.02  
% 3.34/1.02  ------ 
% 3.34/1.02  
% 3.34/1.02  ------ Input Options
% 3.34/1.02  
% 3.34/1.02  --out_options                           all
% 3.34/1.02  --tptp_safe_out                         true
% 3.34/1.02  --problem_path                          ""
% 3.34/1.02  --include_path                          ""
% 3.34/1.02  --clausifier                            res/vclausify_rel
% 3.34/1.02  --clausifier_options                    --mode clausify
% 3.34/1.02  --stdin                                 false
% 3.34/1.02  --stats_out                             all
% 3.34/1.02  
% 3.34/1.02  ------ General Options
% 3.34/1.02  
% 3.34/1.02  --fof                                   false
% 3.34/1.02  --time_out_real                         305.
% 3.34/1.02  --time_out_virtual                      -1.
% 3.34/1.02  --symbol_type_check                     false
% 3.34/1.02  --clausify_out                          false
% 3.34/1.02  --sig_cnt_out                           false
% 3.34/1.02  --trig_cnt_out                          false
% 3.34/1.02  --trig_cnt_out_tolerance                1.
% 3.34/1.02  --trig_cnt_out_sk_spl                   false
% 3.34/1.02  --abstr_cl_out                          false
% 3.34/1.02  
% 3.34/1.02  ------ Global Options
% 3.34/1.02  
% 3.34/1.02  --schedule                              default
% 3.34/1.02  --add_important_lit                     false
% 3.34/1.02  --prop_solver_per_cl                    1000
% 3.34/1.02  --min_unsat_core                        false
% 3.34/1.02  --soft_assumptions                      false
% 3.34/1.02  --soft_lemma_size                       3
% 3.34/1.02  --prop_impl_unit_size                   0
% 3.34/1.02  --prop_impl_unit                        []
% 3.34/1.02  --share_sel_clauses                     true
% 3.34/1.02  --reset_solvers                         false
% 3.34/1.02  --bc_imp_inh                            [conj_cone]
% 3.34/1.02  --conj_cone_tolerance                   3.
% 3.34/1.02  --extra_neg_conj                        none
% 3.34/1.02  --large_theory_mode                     true
% 3.34/1.02  --prolific_symb_bound                   200
% 3.34/1.02  --lt_threshold                          2000
% 3.34/1.02  --clause_weak_htbl                      true
% 3.34/1.02  --gc_record_bc_elim                     false
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing Options
% 3.34/1.02  
% 3.34/1.02  --preprocessing_flag                    true
% 3.34/1.02  --time_out_prep_mult                    0.1
% 3.34/1.02  --splitting_mode                        input
% 3.34/1.02  --splitting_grd                         true
% 3.34/1.02  --splitting_cvd                         false
% 3.34/1.02  --splitting_cvd_svl                     false
% 3.34/1.02  --splitting_nvd                         32
% 3.34/1.02  --sub_typing                            true
% 3.34/1.02  --prep_gs_sim                           true
% 3.34/1.02  --prep_unflatten                        true
% 3.34/1.02  --prep_res_sim                          true
% 3.34/1.02  --prep_upred                            true
% 3.34/1.02  --prep_sem_filter                       exhaustive
% 3.34/1.02  --prep_sem_filter_out                   false
% 3.34/1.02  --pred_elim                             true
% 3.34/1.02  --res_sim_input                         true
% 3.34/1.02  --eq_ax_congr_red                       true
% 3.34/1.02  --pure_diseq_elim                       true
% 3.34/1.02  --brand_transform                       false
% 3.34/1.02  --non_eq_to_eq                          false
% 3.34/1.02  --prep_def_merge                        true
% 3.34/1.02  --prep_def_merge_prop_impl              false
% 3.34/1.02  --prep_def_merge_mbd                    true
% 3.34/1.02  --prep_def_merge_tr_red                 false
% 3.34/1.02  --prep_def_merge_tr_cl                  false
% 3.34/1.02  --smt_preprocessing                     true
% 3.34/1.02  --smt_ac_axioms                         fast
% 3.34/1.02  --preprocessed_out                      false
% 3.34/1.02  --preprocessed_stats                    false
% 3.34/1.02  
% 3.34/1.02  ------ Abstraction refinement Options
% 3.34/1.02  
% 3.34/1.02  --abstr_ref                             []
% 3.34/1.02  --abstr_ref_prep                        false
% 3.34/1.02  --abstr_ref_until_sat                   false
% 3.34/1.02  --abstr_ref_sig_restrict                funpre
% 3.34/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.02  --abstr_ref_under                       []
% 3.34/1.02  
% 3.34/1.02  ------ SAT Options
% 3.34/1.02  
% 3.34/1.02  --sat_mode                              false
% 3.34/1.02  --sat_fm_restart_options                ""
% 3.34/1.02  --sat_gr_def                            false
% 3.34/1.02  --sat_epr_types                         true
% 3.34/1.02  --sat_non_cyclic_types                  false
% 3.34/1.02  --sat_finite_models                     false
% 3.34/1.02  --sat_fm_lemmas                         false
% 3.34/1.02  --sat_fm_prep                           false
% 3.34/1.02  --sat_fm_uc_incr                        true
% 3.34/1.02  --sat_out_model                         small
% 3.34/1.02  --sat_out_clauses                       false
% 3.34/1.02  
% 3.34/1.02  ------ QBF Options
% 3.34/1.02  
% 3.34/1.02  --qbf_mode                              false
% 3.34/1.02  --qbf_elim_univ                         false
% 3.34/1.02  --qbf_dom_inst                          none
% 3.34/1.02  --qbf_dom_pre_inst                      false
% 3.34/1.02  --qbf_sk_in                             false
% 3.34/1.02  --qbf_pred_elim                         true
% 3.34/1.02  --qbf_split                             512
% 3.34/1.02  
% 3.34/1.02  ------ BMC1 Options
% 3.34/1.02  
% 3.34/1.02  --bmc1_incremental                      false
% 3.34/1.02  --bmc1_axioms                           reachable_all
% 3.34/1.02  --bmc1_min_bound                        0
% 3.34/1.02  --bmc1_max_bound                        -1
% 3.34/1.02  --bmc1_max_bound_default                -1
% 3.34/1.02  --bmc1_symbol_reachability              true
% 3.34/1.02  --bmc1_property_lemmas                  false
% 3.34/1.02  --bmc1_k_induction                      false
% 3.34/1.02  --bmc1_non_equiv_states                 false
% 3.34/1.02  --bmc1_deadlock                         false
% 3.34/1.02  --bmc1_ucm                              false
% 3.34/1.02  --bmc1_add_unsat_core                   none
% 3.34/1.02  --bmc1_unsat_core_children              false
% 3.34/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.02  --bmc1_out_stat                         full
% 3.34/1.02  --bmc1_ground_init                      false
% 3.34/1.02  --bmc1_pre_inst_next_state              false
% 3.34/1.02  --bmc1_pre_inst_state                   false
% 3.34/1.02  --bmc1_pre_inst_reach_state             false
% 3.34/1.02  --bmc1_out_unsat_core                   false
% 3.34/1.02  --bmc1_aig_witness_out                  false
% 3.34/1.02  --bmc1_verbose                          false
% 3.34/1.02  --bmc1_dump_clauses_tptp                false
% 3.34/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.02  --bmc1_dump_file                        -
% 3.34/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.02  --bmc1_ucm_extend_mode                  1
% 3.34/1.02  --bmc1_ucm_init_mode                    2
% 3.34/1.02  --bmc1_ucm_cone_mode                    none
% 3.34/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.02  --bmc1_ucm_relax_model                  4
% 3.34/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.02  --bmc1_ucm_layered_model                none
% 3.34/1.02  --bmc1_ucm_max_lemma_size               10
% 3.34/1.02  
% 3.34/1.02  ------ AIG Options
% 3.34/1.02  
% 3.34/1.02  --aig_mode                              false
% 3.34/1.02  
% 3.34/1.02  ------ Instantiation Options
% 3.34/1.02  
% 3.34/1.02  --instantiation_flag                    true
% 3.34/1.02  --inst_sos_flag                         false
% 3.34/1.02  --inst_sos_phase                        true
% 3.34/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.02  --inst_lit_sel_side                     num_symb
% 3.34/1.02  --inst_solver_per_active                1400
% 3.34/1.02  --inst_solver_calls_frac                1.
% 3.34/1.02  --inst_passive_queue_type               priority_queues
% 3.34/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.02  --inst_passive_queues_freq              [25;2]
% 3.34/1.02  --inst_dismatching                      true
% 3.34/1.02  --inst_eager_unprocessed_to_passive     true
% 3.34/1.02  --inst_prop_sim_given                   true
% 3.34/1.02  --inst_prop_sim_new                     false
% 3.34/1.02  --inst_subs_new                         false
% 3.34/1.02  --inst_eq_res_simp                      false
% 3.34/1.02  --inst_subs_given                       false
% 3.34/1.02  --inst_orphan_elimination               true
% 3.34/1.02  --inst_learning_loop_flag               true
% 3.34/1.02  --inst_learning_start                   3000
% 3.34/1.02  --inst_learning_factor                  2
% 3.34/1.02  --inst_start_prop_sim_after_learn       3
% 3.34/1.02  --inst_sel_renew                        solver
% 3.34/1.02  --inst_lit_activity_flag                true
% 3.34/1.02  --inst_restr_to_given                   false
% 3.34/1.02  --inst_activity_threshold               500
% 3.34/1.02  --inst_out_proof                        true
% 3.34/1.02  
% 3.34/1.02  ------ Resolution Options
% 3.34/1.02  
% 3.34/1.02  --resolution_flag                       true
% 3.34/1.02  --res_lit_sel                           adaptive
% 3.34/1.02  --res_lit_sel_side                      none
% 3.34/1.02  --res_ordering                          kbo
% 3.34/1.02  --res_to_prop_solver                    active
% 3.34/1.02  --res_prop_simpl_new                    false
% 3.34/1.02  --res_prop_simpl_given                  true
% 3.34/1.02  --res_passive_queue_type                priority_queues
% 3.34/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.02  --res_passive_queues_freq               [15;5]
% 3.34/1.02  --res_forward_subs                      full
% 3.34/1.02  --res_backward_subs                     full
% 3.34/1.02  --res_forward_subs_resolution           true
% 3.34/1.02  --res_backward_subs_resolution          true
% 3.34/1.02  --res_orphan_elimination                true
% 3.34/1.02  --res_time_limit                        2.
% 3.34/1.02  --res_out_proof                         true
% 3.34/1.02  
% 3.34/1.02  ------ Superposition Options
% 3.34/1.02  
% 3.34/1.02  --superposition_flag                    true
% 3.34/1.02  --sup_passive_queue_type                priority_queues
% 3.34/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.02  --demod_completeness_check              fast
% 3.34/1.02  --demod_use_ground                      true
% 3.34/1.02  --sup_to_prop_solver                    passive
% 3.34/1.02  --sup_prop_simpl_new                    true
% 3.34/1.02  --sup_prop_simpl_given                  true
% 3.34/1.02  --sup_fun_splitting                     false
% 3.34/1.02  --sup_smt_interval                      50000
% 3.34/1.02  
% 3.34/1.02  ------ Superposition Simplification Setup
% 3.34/1.02  
% 3.34/1.02  --sup_indices_passive                   []
% 3.34/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_full_bw                           [BwDemod]
% 3.34/1.02  --sup_immed_triv                        [TrivRules]
% 3.34/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_immed_bw_main                     []
% 3.34/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.02  
% 3.34/1.02  ------ Combination Options
% 3.34/1.02  
% 3.34/1.02  --comb_res_mult                         3
% 3.34/1.02  --comb_sup_mult                         2
% 3.34/1.02  --comb_inst_mult                        10
% 3.34/1.02  
% 3.34/1.02  ------ Debug Options
% 3.34/1.02  
% 3.34/1.02  --dbg_backtrace                         false
% 3.34/1.02  --dbg_dump_prop_clauses                 false
% 3.34/1.02  --dbg_dump_prop_clauses_file            -
% 3.34/1.02  --dbg_out_stat                          false
% 3.34/1.02  ------ Parsing...
% 3.34/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.02  
% 3.34/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.02  ------ Proving...
% 3.34/1.02  ------ Problem Properties 
% 3.34/1.02  
% 3.34/1.02  
% 3.34/1.02  clauses                                 15
% 3.34/1.02  conjectures                             1
% 3.34/1.03  EPR                                     0
% 3.34/1.03  Horn                                    14
% 3.34/1.03  unary                                   5
% 3.34/1.03  binary                                  7
% 3.34/1.03  lits                                    28
% 3.34/1.03  lits eq                                 15
% 3.34/1.03  fd_pure                                 0
% 3.34/1.03  fd_pseudo                               0
% 3.34/1.03  fd_cond                                 0
% 3.34/1.03  fd_pseudo_cond                          0
% 3.34/1.03  AC symbols                              0
% 3.34/1.03  
% 3.34/1.03  ------ Schedule dynamic 5 is on 
% 3.34/1.03  
% 3.34/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  ------ 
% 3.34/1.03  Current options:
% 3.34/1.03  ------ 
% 3.34/1.03  
% 3.34/1.03  ------ Input Options
% 3.34/1.03  
% 3.34/1.03  --out_options                           all
% 3.34/1.03  --tptp_safe_out                         true
% 3.34/1.03  --problem_path                          ""
% 3.34/1.03  --include_path                          ""
% 3.34/1.03  --clausifier                            res/vclausify_rel
% 3.34/1.03  --clausifier_options                    --mode clausify
% 3.34/1.03  --stdin                                 false
% 3.34/1.03  --stats_out                             all
% 3.34/1.03  
% 3.34/1.03  ------ General Options
% 3.34/1.03  
% 3.34/1.03  --fof                                   false
% 3.34/1.03  --time_out_real                         305.
% 3.34/1.03  --time_out_virtual                      -1.
% 3.34/1.03  --symbol_type_check                     false
% 3.34/1.03  --clausify_out                          false
% 3.34/1.03  --sig_cnt_out                           false
% 3.34/1.03  --trig_cnt_out                          false
% 3.34/1.03  --trig_cnt_out_tolerance                1.
% 3.34/1.03  --trig_cnt_out_sk_spl                   false
% 3.34/1.03  --abstr_cl_out                          false
% 3.34/1.03  
% 3.34/1.03  ------ Global Options
% 3.34/1.03  
% 3.34/1.03  --schedule                              default
% 3.34/1.03  --add_important_lit                     false
% 3.34/1.03  --prop_solver_per_cl                    1000
% 3.34/1.03  --min_unsat_core                        false
% 3.34/1.03  --soft_assumptions                      false
% 3.34/1.03  --soft_lemma_size                       3
% 3.34/1.03  --prop_impl_unit_size                   0
% 3.34/1.03  --prop_impl_unit                        []
% 3.34/1.03  --share_sel_clauses                     true
% 3.34/1.03  --reset_solvers                         false
% 3.34/1.03  --bc_imp_inh                            [conj_cone]
% 3.34/1.03  --conj_cone_tolerance                   3.
% 3.34/1.03  --extra_neg_conj                        none
% 3.34/1.03  --large_theory_mode                     true
% 3.34/1.03  --prolific_symb_bound                   200
% 3.34/1.03  --lt_threshold                          2000
% 3.34/1.03  --clause_weak_htbl                      true
% 3.34/1.03  --gc_record_bc_elim                     false
% 3.34/1.03  
% 3.34/1.03  ------ Preprocessing Options
% 3.34/1.03  
% 3.34/1.03  --preprocessing_flag                    true
% 3.34/1.03  --time_out_prep_mult                    0.1
% 3.34/1.03  --splitting_mode                        input
% 3.34/1.03  --splitting_grd                         true
% 3.34/1.03  --splitting_cvd                         false
% 3.34/1.03  --splitting_cvd_svl                     false
% 3.34/1.03  --splitting_nvd                         32
% 3.34/1.03  --sub_typing                            true
% 3.34/1.03  --prep_gs_sim                           true
% 3.34/1.03  --prep_unflatten                        true
% 3.34/1.03  --prep_res_sim                          true
% 3.34/1.03  --prep_upred                            true
% 3.34/1.03  --prep_sem_filter                       exhaustive
% 3.34/1.03  --prep_sem_filter_out                   false
% 3.34/1.03  --pred_elim                             true
% 3.34/1.03  --res_sim_input                         true
% 3.34/1.03  --eq_ax_congr_red                       true
% 3.34/1.03  --pure_diseq_elim                       true
% 3.34/1.03  --brand_transform                       false
% 3.34/1.03  --non_eq_to_eq                          false
% 3.34/1.03  --prep_def_merge                        true
% 3.34/1.03  --prep_def_merge_prop_impl              false
% 3.34/1.03  --prep_def_merge_mbd                    true
% 3.34/1.03  --prep_def_merge_tr_red                 false
% 3.34/1.03  --prep_def_merge_tr_cl                  false
% 3.34/1.03  --smt_preprocessing                     true
% 3.34/1.03  --smt_ac_axioms                         fast
% 3.34/1.03  --preprocessed_out                      false
% 3.34/1.03  --preprocessed_stats                    false
% 3.34/1.03  
% 3.34/1.03  ------ Abstraction refinement Options
% 3.34/1.03  
% 3.34/1.03  --abstr_ref                             []
% 3.34/1.03  --abstr_ref_prep                        false
% 3.34/1.03  --abstr_ref_until_sat                   false
% 3.34/1.03  --abstr_ref_sig_restrict                funpre
% 3.34/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.03  --abstr_ref_under                       []
% 3.34/1.03  
% 3.34/1.03  ------ SAT Options
% 3.34/1.03  
% 3.34/1.03  --sat_mode                              false
% 3.34/1.03  --sat_fm_restart_options                ""
% 3.34/1.03  --sat_gr_def                            false
% 3.34/1.03  --sat_epr_types                         true
% 3.34/1.03  --sat_non_cyclic_types                  false
% 3.34/1.03  --sat_finite_models                     false
% 3.34/1.03  --sat_fm_lemmas                         false
% 3.34/1.03  --sat_fm_prep                           false
% 3.34/1.03  --sat_fm_uc_incr                        true
% 3.34/1.03  --sat_out_model                         small
% 3.34/1.03  --sat_out_clauses                       false
% 3.34/1.03  
% 3.34/1.03  ------ QBF Options
% 3.34/1.03  
% 3.34/1.03  --qbf_mode                              false
% 3.34/1.03  --qbf_elim_univ                         false
% 3.34/1.03  --qbf_dom_inst                          none
% 3.34/1.03  --qbf_dom_pre_inst                      false
% 3.34/1.03  --qbf_sk_in                             false
% 3.34/1.03  --qbf_pred_elim                         true
% 3.34/1.03  --qbf_split                             512
% 3.34/1.03  
% 3.34/1.03  ------ BMC1 Options
% 3.34/1.03  
% 3.34/1.03  --bmc1_incremental                      false
% 3.34/1.03  --bmc1_axioms                           reachable_all
% 3.34/1.03  --bmc1_min_bound                        0
% 3.34/1.03  --bmc1_max_bound                        -1
% 3.34/1.03  --bmc1_max_bound_default                -1
% 3.34/1.03  --bmc1_symbol_reachability              true
% 3.34/1.03  --bmc1_property_lemmas                  false
% 3.34/1.03  --bmc1_k_induction                      false
% 3.34/1.03  --bmc1_non_equiv_states                 false
% 3.34/1.03  --bmc1_deadlock                         false
% 3.34/1.03  --bmc1_ucm                              false
% 3.34/1.03  --bmc1_add_unsat_core                   none
% 3.34/1.03  --bmc1_unsat_core_children              false
% 3.34/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.03  --bmc1_out_stat                         full
% 3.34/1.03  --bmc1_ground_init                      false
% 3.34/1.03  --bmc1_pre_inst_next_state              false
% 3.34/1.03  --bmc1_pre_inst_state                   false
% 3.34/1.03  --bmc1_pre_inst_reach_state             false
% 3.34/1.03  --bmc1_out_unsat_core                   false
% 3.34/1.03  --bmc1_aig_witness_out                  false
% 3.34/1.03  --bmc1_verbose                          false
% 3.34/1.03  --bmc1_dump_clauses_tptp                false
% 3.34/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.03  --bmc1_dump_file                        -
% 3.34/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.03  --bmc1_ucm_extend_mode                  1
% 3.34/1.03  --bmc1_ucm_init_mode                    2
% 3.34/1.03  --bmc1_ucm_cone_mode                    none
% 3.34/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.03  --bmc1_ucm_relax_model                  4
% 3.34/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.03  --bmc1_ucm_layered_model                none
% 3.34/1.03  --bmc1_ucm_max_lemma_size               10
% 3.34/1.03  
% 3.34/1.03  ------ AIG Options
% 3.34/1.03  
% 3.34/1.03  --aig_mode                              false
% 3.34/1.03  
% 3.34/1.03  ------ Instantiation Options
% 3.34/1.03  
% 3.34/1.03  --instantiation_flag                    true
% 3.34/1.03  --inst_sos_flag                         false
% 3.34/1.03  --inst_sos_phase                        true
% 3.34/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.03  --inst_lit_sel_side                     none
% 3.34/1.03  --inst_solver_per_active                1400
% 3.34/1.03  --inst_solver_calls_frac                1.
% 3.34/1.03  --inst_passive_queue_type               priority_queues
% 3.34/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.03  --inst_passive_queues_freq              [25;2]
% 3.34/1.03  --inst_dismatching                      true
% 3.34/1.03  --inst_eager_unprocessed_to_passive     true
% 3.34/1.03  --inst_prop_sim_given                   true
% 3.34/1.03  --inst_prop_sim_new                     false
% 3.34/1.03  --inst_subs_new                         false
% 3.34/1.03  --inst_eq_res_simp                      false
% 3.34/1.03  --inst_subs_given                       false
% 3.34/1.03  --inst_orphan_elimination               true
% 3.34/1.03  --inst_learning_loop_flag               true
% 3.34/1.03  --inst_learning_start                   3000
% 3.34/1.03  --inst_learning_factor                  2
% 3.34/1.03  --inst_start_prop_sim_after_learn       3
% 3.34/1.03  --inst_sel_renew                        solver
% 3.34/1.03  --inst_lit_activity_flag                true
% 3.34/1.03  --inst_restr_to_given                   false
% 3.34/1.03  --inst_activity_threshold               500
% 3.34/1.03  --inst_out_proof                        true
% 3.34/1.03  
% 3.34/1.03  ------ Resolution Options
% 3.34/1.03  
% 3.34/1.03  --resolution_flag                       false
% 3.34/1.03  --res_lit_sel                           adaptive
% 3.34/1.03  --res_lit_sel_side                      none
% 3.34/1.03  --res_ordering                          kbo
% 3.34/1.03  --res_to_prop_solver                    active
% 3.34/1.03  --res_prop_simpl_new                    false
% 3.34/1.03  --res_prop_simpl_given                  true
% 3.34/1.03  --res_passive_queue_type                priority_queues
% 3.34/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.03  --res_passive_queues_freq               [15;5]
% 3.34/1.03  --res_forward_subs                      full
% 3.34/1.03  --res_backward_subs                     full
% 3.34/1.03  --res_forward_subs_resolution           true
% 3.34/1.03  --res_backward_subs_resolution          true
% 3.34/1.03  --res_orphan_elimination                true
% 3.34/1.03  --res_time_limit                        2.
% 3.34/1.03  --res_out_proof                         true
% 3.34/1.03  
% 3.34/1.03  ------ Superposition Options
% 3.34/1.03  
% 3.34/1.03  --superposition_flag                    true
% 3.34/1.03  --sup_passive_queue_type                priority_queues
% 3.34/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.03  --demod_completeness_check              fast
% 3.34/1.03  --demod_use_ground                      true
% 3.34/1.03  --sup_to_prop_solver                    passive
% 3.34/1.03  --sup_prop_simpl_new                    true
% 3.34/1.03  --sup_prop_simpl_given                  true
% 3.34/1.03  --sup_fun_splitting                     false
% 3.34/1.03  --sup_smt_interval                      50000
% 3.34/1.03  
% 3.34/1.03  ------ Superposition Simplification Setup
% 3.34/1.03  
% 3.34/1.03  --sup_indices_passive                   []
% 3.34/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.03  --sup_full_bw                           [BwDemod]
% 3.34/1.03  --sup_immed_triv                        [TrivRules]
% 3.34/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.03  --sup_immed_bw_main                     []
% 3.34/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.03  
% 3.34/1.03  ------ Combination Options
% 3.34/1.03  
% 3.34/1.03  --comb_res_mult                         3
% 3.34/1.03  --comb_sup_mult                         2
% 3.34/1.03  --comb_inst_mult                        10
% 3.34/1.03  
% 3.34/1.03  ------ Debug Options
% 3.34/1.03  
% 3.34/1.03  --dbg_backtrace                         false
% 3.34/1.03  --dbg_dump_prop_clauses                 false
% 3.34/1.03  --dbg_dump_prop_clauses_file            -
% 3.34/1.03  --dbg_out_stat                          false
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  ------ Proving...
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  % SZS status Theorem for theBenchmark.p
% 3.34/1.03  
% 3.34/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.03  
% 3.34/1.03  fof(f6,axiom,(
% 3.34/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f41,plain,(
% 3.34/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f6])).
% 3.34/1.03  
% 3.34/1.03  fof(f5,axiom,(
% 3.34/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f40,plain,(
% 3.34/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.34/1.03    inference(cnf_transformation,[],[f5])).
% 3.34/1.03  
% 3.34/1.03  fof(f8,axiom,(
% 3.34/1.03    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f19,plain,(
% 3.34/1.03    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/1.03    inference(ennf_transformation,[],[f8])).
% 3.34/1.03  
% 3.34/1.03  fof(f43,plain,(
% 3.34/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f19])).
% 3.34/1.03  
% 3.34/1.03  fof(f1,axiom,(
% 3.34/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f36,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f1])).
% 3.34/1.03  
% 3.34/1.03  fof(f59,plain,(
% 3.34/1.03    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/1.03    inference(definition_unfolding,[],[f43,f36])).
% 3.34/1.03  
% 3.34/1.03  fof(f15,conjecture,(
% 3.34/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f16,negated_conjecture,(
% 3.34/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.34/1.03    inference(negated_conjecture,[],[f15])).
% 3.34/1.03  
% 3.34/1.03  fof(f29,plain,(
% 3.34/1.03    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.34/1.03    inference(ennf_transformation,[],[f16])).
% 3.34/1.03  
% 3.34/1.03  fof(f30,plain,(
% 3.34/1.03    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.34/1.03    inference(flattening,[],[f29])).
% 3.34/1.03  
% 3.34/1.03  fof(f31,plain,(
% 3.34/1.03    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.34/1.03    inference(nnf_transformation,[],[f30])).
% 3.34/1.03  
% 3.34/1.03  fof(f32,plain,(
% 3.34/1.03    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.34/1.03    inference(flattening,[],[f31])).
% 3.34/1.03  
% 3.34/1.03  fof(f34,plain,(
% 3.34/1.03    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.34/1.03    introduced(choice_axiom,[])).
% 3.34/1.03  
% 3.34/1.03  fof(f33,plain,(
% 3.34/1.03    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.34/1.03    introduced(choice_axiom,[])).
% 3.34/1.03  
% 3.34/1.03  fof(f35,plain,(
% 3.34/1.03    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.34/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 3.34/1.03  
% 3.34/1.03  fof(f53,plain,(
% 3.34/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.34/1.03    inference(cnf_transformation,[],[f35])).
% 3.34/1.03  
% 3.34/1.03  fof(f54,plain,(
% 3.34/1.03    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.34/1.03    inference(cnf_transformation,[],[f35])).
% 3.34/1.03  
% 3.34/1.03  fof(f9,axiom,(
% 3.34/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f20,plain,(
% 3.34/1.03    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.03    inference(ennf_transformation,[],[f9])).
% 3.34/1.03  
% 3.34/1.03  fof(f21,plain,(
% 3.34/1.03    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.03    inference(flattening,[],[f20])).
% 3.34/1.03  
% 3.34/1.03  fof(f44,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f21])).
% 3.34/1.03  
% 3.34/1.03  fof(f52,plain,(
% 3.34/1.03    l1_pre_topc(sK0)),
% 3.34/1.03    inference(cnf_transformation,[],[f35])).
% 3.34/1.03  
% 3.34/1.03  fof(f14,axiom,(
% 3.34/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f28,plain,(
% 3.34/1.03    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.03    inference(ennf_transformation,[],[f14])).
% 3.34/1.03  
% 3.34/1.03  fof(f50,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f28])).
% 3.34/1.03  
% 3.34/1.03  fof(f3,axiom,(
% 3.34/1.03    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f38,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f3])).
% 3.34/1.03  
% 3.34/1.03  fof(f56,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.34/1.03    inference(definition_unfolding,[],[f38,f36,f36])).
% 3.34/1.03  
% 3.34/1.03  fof(f2,axiom,(
% 3.34/1.03    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f37,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.34/1.03    inference(cnf_transformation,[],[f2])).
% 3.34/1.03  
% 3.34/1.03  fof(f4,axiom,(
% 3.34/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f39,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f4])).
% 3.34/1.03  
% 3.34/1.03  fof(f57,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0) )),
% 3.34/1.03    inference(definition_unfolding,[],[f37,f39])).
% 3.34/1.03  
% 3.34/1.03  fof(f10,axiom,(
% 3.34/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f22,plain,(
% 3.34/1.03    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.34/1.03    inference(ennf_transformation,[],[f10])).
% 3.34/1.03  
% 3.34/1.03  fof(f23,plain,(
% 3.34/1.03    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.34/1.03    inference(flattening,[],[f22])).
% 3.34/1.03  
% 3.34/1.03  fof(f46,plain,(
% 3.34/1.03    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f23])).
% 3.34/1.03  
% 3.34/1.03  fof(f7,axiom,(
% 3.34/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f17,plain,(
% 3.34/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.34/1.03    inference(ennf_transformation,[],[f7])).
% 3.34/1.03  
% 3.34/1.03  fof(f18,plain,(
% 3.34/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/1.03    inference(flattening,[],[f17])).
% 3.34/1.03  
% 3.34/1.03  fof(f42,plain,(
% 3.34/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f18])).
% 3.34/1.03  
% 3.34/1.03  fof(f58,plain,(
% 3.34/1.03    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/1.03    inference(definition_unfolding,[],[f42,f39])).
% 3.34/1.03  
% 3.34/1.03  fof(f13,axiom,(
% 3.34/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f27,plain,(
% 3.34/1.03    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.03    inference(ennf_transformation,[],[f13])).
% 3.34/1.03  
% 3.34/1.03  fof(f49,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f27])).
% 3.34/1.03  
% 3.34/1.03  fof(f12,axiom,(
% 3.34/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f26,plain,(
% 3.34/1.03    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.03    inference(ennf_transformation,[],[f12])).
% 3.34/1.03  
% 3.34/1.03  fof(f48,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f26])).
% 3.34/1.03  
% 3.34/1.03  fof(f55,plain,(
% 3.34/1.03    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.34/1.03    inference(cnf_transformation,[],[f35])).
% 3.34/1.03  
% 3.34/1.03  fof(f45,plain,(
% 3.34/1.03    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f21])).
% 3.34/1.03  
% 3.34/1.03  fof(f51,plain,(
% 3.34/1.03    v2_pre_topc(sK0)),
% 3.34/1.03    inference(cnf_transformation,[],[f35])).
% 3.34/1.03  
% 3.34/1.03  cnf(c_3,plain,
% 3.34/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.34/1.03      inference(cnf_transformation,[],[f41]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_822,plain,
% 3.34/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_2,plain,
% 3.34/1.03      ( k2_subset_1(X0) = X0 ),
% 3.34/1.03      inference(cnf_transformation,[],[f40]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_827,plain,
% 3.34/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.34/1.03      inference(light_normalisation,[status(thm)],[c_822,c_2]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_5,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/1.03      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 3.34/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_820,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 3.34/1.03      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_2001,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_827,c_820]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_15,negated_conjecture,
% 3.34/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.34/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_819,plain,
% 3.34/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1999,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_819,c_820]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_3387,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_2001,c_1999]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_14,negated_conjecture,
% 3.34/1.03      ( v4_pre_topc(sK1,sK0)
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_121,plain,
% 3.34/1.03      ( v4_pre_topc(sK1,sK0)
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_7,plain,
% 3.34/1.03      ( ~ v4_pre_topc(X0,X1)
% 3.34/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | ~ l1_pre_topc(X1)
% 3.34/1.03      | k2_pre_topc(X1,X0) = X0 ),
% 3.34/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_16,negated_conjecture,
% 3.34/1.03      ( l1_pre_topc(sK0) ),
% 3.34/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_311,plain,
% 3.34/1.03      ( ~ v4_pre_topc(X0,X1)
% 3.34/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | k2_pre_topc(X1,X0) = X0
% 3.34/1.03      | sK0 != X1 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_312,plain,
% 3.34/1.03      ( ~ v4_pre_topc(X0,sK0)
% 3.34/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k2_pre_topc(sK0,X0) = X0 ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_311]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_361,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.34/1.03      | k2_pre_topc(sK0,X0) = X0
% 3.34/1.03      | sK1 != X0
% 3.34/1.03      | sK0 != sK0 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_121,c_312]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_362,plain,
% 3.34/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.34/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_361]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_364,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.34/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.34/1.03      inference(global_propositional_subsumption,
% 3.34/1.03                [status(thm)],
% 3.34/1.03                [c_362,c_15]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_451,plain,
% 3.34/1.03      ( k2_pre_topc(sK0,sK1) = sK1
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(prop_impl,[status(thm)],[c_364]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_452,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.34/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.34/1.03      inference(renaming,[status(thm)],[c_451]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_3578,plain,
% 3.34/1.03      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.34/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_3387,c_452]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_12,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | ~ l1_pre_topc(X1)
% 3.34/1.03      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.34/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_263,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 3.34/1.03      | sK0 != X1 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_264,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_263]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_818,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 3.34/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_975,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_819,c_818]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_2252,plain,
% 3.34/1.03      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_1999,c_975]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_0,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.34/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_2312,plain,
% 3.34/1.03      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_2252,c_0]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_3418,plain,
% 3.34/1.03      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_2001,c_2312]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_4740,plain,
% 3.34/1.03      ( k2_pre_topc(sK0,sK1) = sK1
% 3.34/1.03      | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_3578,c_3418]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1,plain,
% 3.34/1.03      ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
% 3.34/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_4745,plain,
% 3.34/1.03      ( k2_pre_topc(sK0,sK1) = sK1
% 3.34/1.03      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_4740,c_1]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_8,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | ~ l1_pre_topc(X1) ),
% 3.34/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_299,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | sK0 != X1 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_300,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_299]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_815,plain,
% 3.34/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.34/1.03      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_4,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.34/1.03      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.34/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_821,plain,
% 3.34/1.03      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.34/1.03      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.34/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_2666,plain,
% 3.34/1.03      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
% 3.34/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.34/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_815,c_821]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_5087,plain,
% 3.34/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.34/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_819,c_2666]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_5279,plain,
% 3.34/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_819,c_5087]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_11,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | ~ l1_pre_topc(X1)
% 3.34/1.03      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.34/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_275,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 3.34/1.03      | sK0 != X1 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_276,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_275]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_817,plain,
% 3.34/1.03      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 3.34/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_950,plain,
% 3.34/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_819,c_817]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_5289,plain,
% 3.34/1.03      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.34/1.03      inference(light_normalisation,[status(thm)],[c_5279,c_950]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_5495,plain,
% 3.34/1.03      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_4745,c_5289]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_10,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | ~ l1_pre_topc(X1)
% 3.34/1.03      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.34/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_287,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.34/1.03      | sK0 != X1 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_288,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_287]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_816,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 3.34/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1041,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_819,c_816]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_6052,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_5495,c_1041]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_13,negated_conjecture,
% 3.34/1.03      ( ~ v4_pre_topc(sK1,sK0)
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_119,plain,
% 3.34/1.03      ( ~ v4_pre_topc(sK1,sK0)
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.34/1.03      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_6,plain,
% 3.34/1.03      ( v4_pre_topc(X0,X1)
% 3.34/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | ~ l1_pre_topc(X1)
% 3.34/1.03      | ~ v2_pre_topc(X1)
% 3.34/1.03      | k2_pre_topc(X1,X0) != X0 ),
% 3.34/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_17,negated_conjecture,
% 3.34/1.03      ( v2_pre_topc(sK0) ),
% 3.34/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_235,plain,
% 3.34/1.03      ( v4_pre_topc(X0,X1)
% 3.34/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.03      | ~ l1_pre_topc(X1)
% 3.34/1.03      | k2_pre_topc(X1,X0) != X0
% 3.34/1.03      | sK0 != X1 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_236,plain,
% 3.34/1.03      ( v4_pre_topc(X0,sK0)
% 3.34/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | ~ l1_pre_topc(sK0)
% 3.34/1.03      | k2_pre_topc(sK0,X0) != X0 ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_235]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_240,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | v4_pre_topc(X0,sK0)
% 3.34/1.03      | k2_pre_topc(sK0,X0) != X0 ),
% 3.34/1.03      inference(global_propositional_subsumption,
% 3.34/1.03                [status(thm)],
% 3.34/1.03                [c_236,c_16]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_241,plain,
% 3.34/1.03      ( v4_pre_topc(X0,sK0)
% 3.34/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k2_pre_topc(sK0,X0) != X0 ),
% 3.34/1.03      inference(renaming,[status(thm)],[c_240]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_372,plain,
% 3.34/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.34/1.03      | k2_pre_topc(sK0,X0) != X0
% 3.34/1.03      | sK1 != X0
% 3.34/1.03      | sK0 != sK0 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_119,c_241]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_373,plain,
% 3.34/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.34/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.34/1.03      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_372]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_375,plain,
% 3.34/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.34/1.03      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.34/1.03      inference(global_propositional_subsumption,
% 3.34/1.03                [status(thm)],
% 3.34/1.03                [c_373,c_15]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(contradiction,plain,
% 3.34/1.03      ( $false ),
% 3.34/1.03      inference(minisat,[status(thm)],[c_6052,c_5495,c_375]) ).
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.03  
% 3.34/1.03  ------                               Statistics
% 3.34/1.03  
% 3.34/1.03  ------ General
% 3.34/1.03  
% 3.34/1.03  abstr_ref_over_cycles:                  0
% 3.34/1.03  abstr_ref_under_cycles:                 0
% 3.34/1.03  gc_basic_clause_elim:                   0
% 3.34/1.03  forced_gc_time:                         0
% 3.34/1.03  parsing_time:                           0.025
% 3.34/1.03  unif_index_cands_time:                  0.
% 3.34/1.03  unif_index_add_time:                    0.
% 3.34/1.03  orderings_time:                         0.
% 3.34/1.03  out_proof_time:                         0.008
% 3.34/1.03  total_time:                             0.244
% 3.34/1.03  num_of_symbols:                         49
% 3.34/1.03  num_of_terms:                           6448
% 3.34/1.03  
% 3.34/1.03  ------ Preprocessing
% 3.34/1.03  
% 3.34/1.03  num_of_splits:                          0
% 3.34/1.03  num_of_split_atoms:                     0
% 3.34/1.03  num_of_reused_defs:                     0
% 3.34/1.03  num_eq_ax_congr_red:                    17
% 3.34/1.03  num_of_sem_filtered_clauses:            1
% 3.34/1.03  num_of_subtypes:                        0
% 3.34/1.03  monotx_restored_types:                  0
% 3.34/1.03  sat_num_of_epr_types:                   0
% 3.34/1.03  sat_num_of_non_cyclic_types:            0
% 3.34/1.03  sat_guarded_non_collapsed_types:        0
% 3.34/1.03  num_pure_diseq_elim:                    0
% 3.34/1.03  simp_replaced_by:                       0
% 3.34/1.03  res_preprocessed:                       92
% 3.34/1.03  prep_upred:                             0
% 3.34/1.03  prep_unflattend:                        10
% 3.34/1.03  smt_new_axioms:                         0
% 3.34/1.03  pred_elim_cands:                        1
% 3.34/1.03  pred_elim:                              3
% 3.34/1.03  pred_elim_cl:                           3
% 3.34/1.03  pred_elim_cycles:                       5
% 3.34/1.03  merged_defs:                            8
% 3.34/1.03  merged_defs_ncl:                        0
% 3.34/1.03  bin_hyper_res:                          9
% 3.34/1.03  prep_cycles:                            4
% 3.34/1.03  pred_elim_time:                         0.004
% 3.34/1.03  splitting_time:                         0.
% 3.34/1.03  sem_filter_time:                        0.
% 3.34/1.03  monotx_time:                            0.
% 3.34/1.03  subtype_inf_time:                       0.
% 3.34/1.03  
% 3.34/1.03  ------ Problem properties
% 3.34/1.03  
% 3.34/1.03  clauses:                                15
% 3.34/1.03  conjectures:                            1
% 3.34/1.03  epr:                                    0
% 3.34/1.03  horn:                                   14
% 3.34/1.03  ground:                                 3
% 3.34/1.03  unary:                                  5
% 3.34/1.03  binary:                                 7
% 3.34/1.03  lits:                                   28
% 3.34/1.03  lits_eq:                                15
% 3.34/1.03  fd_pure:                                0
% 3.34/1.03  fd_pseudo:                              0
% 3.34/1.03  fd_cond:                                0
% 3.34/1.03  fd_pseudo_cond:                         0
% 3.34/1.03  ac_symbols:                             0
% 3.34/1.03  
% 3.34/1.03  ------ Propositional Solver
% 3.34/1.03  
% 3.34/1.03  prop_solver_calls:                      29
% 3.34/1.03  prop_fast_solver_calls:                 575
% 3.34/1.03  smt_solver_calls:                       0
% 3.34/1.03  smt_fast_solver_calls:                  0
% 3.34/1.03  prop_num_of_clauses:                    2532
% 3.34/1.03  prop_preprocess_simplified:             4915
% 3.34/1.03  prop_fo_subsumed:                       4
% 3.34/1.03  prop_solver_time:                       0.
% 3.34/1.03  smt_solver_time:                        0.
% 3.34/1.03  smt_fast_solver_time:                   0.
% 3.34/1.03  prop_fast_solver_time:                  0.
% 3.34/1.03  prop_unsat_core_time:                   0.
% 3.34/1.03  
% 3.34/1.03  ------ QBF
% 3.34/1.03  
% 3.34/1.03  qbf_q_res:                              0
% 3.34/1.03  qbf_num_tautologies:                    0
% 3.34/1.03  qbf_prep_cycles:                        0
% 3.34/1.03  
% 3.34/1.03  ------ BMC1
% 3.34/1.03  
% 3.34/1.03  bmc1_current_bound:                     -1
% 3.34/1.03  bmc1_last_solved_bound:                 -1
% 3.34/1.03  bmc1_unsat_core_size:                   -1
% 3.34/1.03  bmc1_unsat_core_parents_size:           -1
% 3.34/1.03  bmc1_merge_next_fun:                    0
% 3.34/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.34/1.03  
% 3.34/1.03  ------ Instantiation
% 3.34/1.03  
% 3.34/1.03  inst_num_of_clauses:                    849
% 3.34/1.03  inst_num_in_passive:                    86
% 3.34/1.03  inst_num_in_active:                     481
% 3.34/1.03  inst_num_in_unprocessed:                282
% 3.34/1.03  inst_num_of_loops:                      490
% 3.34/1.03  inst_num_of_learning_restarts:          0
% 3.34/1.03  inst_num_moves_active_passive:          5
% 3.34/1.03  inst_lit_activity:                      0
% 3.34/1.03  inst_lit_activity_moves:                0
% 3.34/1.03  inst_num_tautologies:                   0
% 3.34/1.03  inst_num_prop_implied:                  0
% 3.34/1.03  inst_num_existing_simplified:           0
% 3.34/1.03  inst_num_eq_res_simplified:             0
% 3.34/1.03  inst_num_child_elim:                    0
% 3.34/1.03  inst_num_of_dismatching_blockings:      293
% 3.34/1.03  inst_num_of_non_proper_insts:           639
% 3.34/1.03  inst_num_of_duplicates:                 0
% 3.34/1.03  inst_inst_num_from_inst_to_res:         0
% 3.34/1.03  inst_dismatching_checking_time:         0.
% 3.34/1.03  
% 3.34/1.03  ------ Resolution
% 3.34/1.03  
% 3.34/1.03  res_num_of_clauses:                     0
% 3.34/1.03  res_num_in_passive:                     0
% 3.34/1.03  res_num_in_active:                      0
% 3.34/1.03  res_num_of_loops:                       96
% 3.34/1.03  res_forward_subset_subsumed:            21
% 3.34/1.03  res_backward_subset_subsumed:           0
% 3.34/1.03  res_forward_subsumed:                   0
% 3.34/1.03  res_backward_subsumed:                  0
% 3.34/1.03  res_forward_subsumption_resolution:     0
% 3.34/1.03  res_backward_subsumption_resolution:    0
% 3.34/1.03  res_clause_to_clause_subsumption:       360
% 3.34/1.03  res_orphan_elimination:                 0
% 3.34/1.03  res_tautology_del:                      66
% 3.34/1.03  res_num_eq_res_simplified:              1
% 3.34/1.03  res_num_sel_changes:                    0
% 3.34/1.03  res_moves_from_active_to_pass:          0
% 3.34/1.03  
% 3.34/1.03  ------ Superposition
% 3.34/1.03  
% 3.34/1.03  sup_time_total:                         0.
% 3.34/1.03  sup_time_generating:                    0.
% 3.34/1.03  sup_time_sim_full:                      0.
% 3.34/1.03  sup_time_sim_immed:                     0.
% 3.34/1.03  
% 3.34/1.03  sup_num_of_clauses:                     149
% 3.34/1.03  sup_num_in_active:                      80
% 3.34/1.03  sup_num_in_passive:                     69
% 3.34/1.03  sup_num_of_loops:                       96
% 3.34/1.03  sup_fw_superposition:                   150
% 3.34/1.03  sup_bw_superposition:                   125
% 3.34/1.03  sup_immediate_simplified:               27
% 3.34/1.03  sup_given_eliminated:                   1
% 3.34/1.03  comparisons_done:                       0
% 3.34/1.03  comparisons_avoided:                    6
% 3.34/1.03  
% 3.34/1.03  ------ Simplifications
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  sim_fw_subset_subsumed:                 0
% 3.34/1.03  sim_bw_subset_subsumed:                 6
% 3.34/1.03  sim_fw_subsumed:                        2
% 3.34/1.03  sim_bw_subsumed:                        0
% 3.34/1.03  sim_fw_subsumption_res:                 0
% 3.34/1.03  sim_bw_subsumption_res:                 0
% 3.34/1.03  sim_tautology_del:                      1
% 3.34/1.03  sim_eq_tautology_del:                   18
% 3.34/1.03  sim_eq_res_simp:                        0
% 3.34/1.03  sim_fw_demodulated:                     6
% 3.34/1.03  sim_bw_demodulated:                     13
% 3.34/1.03  sim_light_normalised:                   26
% 3.34/1.03  sim_joinable_taut:                      0
% 3.34/1.03  sim_joinable_simp:                      0
% 3.34/1.03  sim_ac_normalised:                      0
% 3.34/1.03  sim_smt_subsumption:                    0
% 3.34/1.03  
%------------------------------------------------------------------------------

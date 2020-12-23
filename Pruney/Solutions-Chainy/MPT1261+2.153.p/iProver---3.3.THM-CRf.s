%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:46 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  133 (1186 expanded)
%              Number of clauses        :   70 ( 358 expanded)
%              Number of leaves         :   18 ( 268 expanded)
%              Depth                    :   19
%              Number of atoms          :  337 (4201 expanded)
%              Number of equality atoms :  163 (1558 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_691,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_702,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_691,c_2])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_689,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1266,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_702,c_689])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_678,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1265,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_678,c_689])).

cnf(c_1707,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1266,c_1265])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_679,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1717,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1707,c_679])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_685,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2231,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_685])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2497,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2231,c_20])).

cnf(c_2498,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2497])).

cnf(c_2820,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1717,c_2498])).

cnf(c_0,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_693,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1706,plain,
    ( r1_tarski(k7_subset_1(X0,X0,X1),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1266,c_693])).

cnf(c_3858,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2820,c_1706])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_690,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1995,plain,
    ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_690])).

cnf(c_4155,plain,
    ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_1995])).

cnf(c_5306,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3858,c_4155])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1994,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_690])).

cnf(c_2631,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_1994])).

cnf(c_3571,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2631,c_20])).

cnf(c_3572,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3571])).

cnf(c_3581,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_678,c_3572])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_681,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1151,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_681])).

cnf(c_954,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1527,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1151,c_17,c_16,c_954])).

cnf(c_3586,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3581,c_1527])).

cnf(c_5314,plain,
    ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5306,c_3586])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k2_subset_1(X1)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_688,plain,
    ( k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_711,plain,
    ( k4_subset_1(X0,X1,X0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_688,c_2])).

cnf(c_1246,plain,
    ( k4_subset_1(X0,X1,X0) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_711])).

cnf(c_5307,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3858,c_1246])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_692,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2035,plain,
    ( k4_subset_1(X0,X0,X1) = k4_subset_1(X0,X1,X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_692])).

cnf(c_4917,plain,
    ( k4_subset_1(X0,X0,X1) = k4_subset_1(X0,X1,X0)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_2035])).

cnf(c_5305,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3858,c_4917])).

cnf(c_6865,plain,
    ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_5307,c_5305])).

cnf(c_8655,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_5314,c_6865])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_682,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1835,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_682])).

cnf(c_960,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2504,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1835,c_17,c_16,c_960])).

cnf(c_9360,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_8655,c_2504])).

cnf(c_8,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_915,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9360,c_8655,c_915,c_14,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:37:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.04  
% 3.62/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.04  
% 3.62/1.04  ------  iProver source info
% 3.62/1.04  
% 3.62/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.04  git: non_committed_changes: false
% 3.62/1.04  git: last_make_outside_of_git: false
% 3.62/1.04  
% 3.62/1.04  ------ 
% 3.62/1.04  ------ Parsing...
% 3.62/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.04  
% 3.62/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.04  ------ Proving...
% 3.62/1.04  ------ Problem Properties 
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  clauses                                 19
% 3.62/1.04  conjectures                             5
% 3.62/1.04  EPR                                     2
% 3.62/1.04  Horn                                    18
% 3.62/1.04  unary                                   6
% 3.62/1.04  binary                                  5
% 3.62/1.04  lits                                    44
% 3.62/1.04  lits eq                                 11
% 3.62/1.04  fd_pure                                 0
% 3.62/1.04  fd_pseudo                               0
% 3.62/1.04  fd_cond                                 0
% 3.62/1.04  fd_pseudo_cond                          0
% 3.62/1.04  AC symbols                              0
% 3.62/1.04  
% 3.62/1.04  ------ Input Options Time Limit: Unbounded
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  ------ 
% 3.62/1.04  Current options:
% 3.62/1.04  ------ 
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  ------ Proving...
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  % SZS status Theorem for theBenchmark.p
% 3.62/1.04  
% 3.62/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.04  
% 3.62/1.04  fof(f6,axiom,(
% 3.62/1.04    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f47,plain,(
% 3.62/1.04    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f6])).
% 3.62/1.04  
% 3.62/1.04  fof(f5,axiom,(
% 3.62/1.04    ! [X0] : k2_subset_1(X0) = X0),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f46,plain,(
% 3.62/1.04    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.62/1.04    inference(cnf_transformation,[],[f5])).
% 3.62/1.04  
% 3.62/1.04  fof(f8,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f24,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/1.04    inference(ennf_transformation,[],[f8])).
% 3.62/1.04  
% 3.62/1.04  fof(f49,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f24])).
% 3.62/1.04  
% 3.62/1.04  fof(f1,axiom,(
% 3.62/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f42,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f1])).
% 3.62/1.04  
% 3.62/1.04  fof(f10,axiom,(
% 3.62/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f51,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f10])).
% 3.62/1.04  
% 3.62/1.04  fof(f64,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.62/1.04    inference(definition_unfolding,[],[f42,f51])).
% 3.62/1.04  
% 3.62/1.04  fof(f67,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/1.04    inference(definition_unfolding,[],[f49,f64])).
% 3.62/1.04  
% 3.62/1.04  fof(f17,conjecture,(
% 3.62/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f18,negated_conjecture,(
% 3.62/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.62/1.04    inference(negated_conjecture,[],[f17])).
% 3.62/1.04  
% 3.62/1.04  fof(f35,plain,(
% 3.62/1.04    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.62/1.04    inference(ennf_transformation,[],[f18])).
% 3.62/1.04  
% 3.62/1.04  fof(f36,plain,(
% 3.62/1.04    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.62/1.04    inference(flattening,[],[f35])).
% 3.62/1.04  
% 3.62/1.04  fof(f37,plain,(
% 3.62/1.04    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.62/1.04    inference(nnf_transformation,[],[f36])).
% 3.62/1.04  
% 3.62/1.04  fof(f38,plain,(
% 3.62/1.04    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.62/1.04    inference(flattening,[],[f37])).
% 3.62/1.04  
% 3.62/1.04  fof(f40,plain,(
% 3.62/1.04    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.62/1.04    introduced(choice_axiom,[])).
% 3.62/1.04  
% 3.62/1.04  fof(f39,plain,(
% 3.62/1.04    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.62/1.04    introduced(choice_axiom,[])).
% 3.62/1.04  
% 3.62/1.04  fof(f41,plain,(
% 3.62/1.04    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.62/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 3.62/1.04  
% 3.62/1.04  fof(f61,plain,(
% 3.62/1.04    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.62/1.04    inference(cnf_transformation,[],[f41])).
% 3.62/1.04  
% 3.62/1.04  fof(f62,plain,(
% 3.62/1.04    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.62/1.04    inference(cnf_transformation,[],[f41])).
% 3.62/1.04  
% 3.62/1.04  fof(f12,axiom,(
% 3.62/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f27,plain,(
% 3.62/1.04    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.04    inference(ennf_transformation,[],[f12])).
% 3.62/1.04  
% 3.62/1.04  fof(f28,plain,(
% 3.62/1.04    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.04    inference(flattening,[],[f27])).
% 3.62/1.04  
% 3.62/1.04  fof(f53,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f28])).
% 3.62/1.04  
% 3.62/1.04  fof(f60,plain,(
% 3.62/1.04    l1_pre_topc(sK0)),
% 3.62/1.04    inference(cnf_transformation,[],[f41])).
% 3.62/1.04  
% 3.62/1.04  fof(f2,axiom,(
% 3.62/1.04    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f43,plain,(
% 3.62/1.04    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f2])).
% 3.62/1.04  
% 3.62/1.04  fof(f65,plain,(
% 3.62/1.04    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 3.62/1.04    inference(definition_unfolding,[],[f43,f64])).
% 3.62/1.04  
% 3.62/1.04  fof(f11,axiom,(
% 3.62/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f19,plain,(
% 3.62/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.62/1.04    inference(unused_predicate_definition_removal,[],[f11])).
% 3.62/1.04  
% 3.62/1.04  fof(f26,plain,(
% 3.62/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.62/1.04    inference(ennf_transformation,[],[f19])).
% 3.62/1.04  
% 3.62/1.04  fof(f52,plain,(
% 3.62/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f26])).
% 3.62/1.04  
% 3.62/1.04  fof(f7,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f22,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.62/1.04    inference(ennf_transformation,[],[f7])).
% 3.62/1.04  
% 3.62/1.04  fof(f23,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/1.04    inference(flattening,[],[f22])).
% 3.62/1.04  
% 3.62/1.04  fof(f48,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f23])).
% 3.62/1.04  
% 3.62/1.04  fof(f3,axiom,(
% 3.62/1.04    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f44,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f3])).
% 3.62/1.04  
% 3.62/1.04  fof(f66,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/1.04    inference(definition_unfolding,[],[f48,f44])).
% 3.62/1.04  
% 3.62/1.04  fof(f13,axiom,(
% 3.62/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f29,plain,(
% 3.62/1.04    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.62/1.04    inference(ennf_transformation,[],[f13])).
% 3.62/1.04  
% 3.62/1.04  fof(f30,plain,(
% 3.62/1.04    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.62/1.04    inference(flattening,[],[f29])).
% 3.62/1.04  
% 3.62/1.04  fof(f55,plain,(
% 3.62/1.04    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f30])).
% 3.62/1.04  
% 3.62/1.04  fof(f16,axiom,(
% 3.62/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f34,plain,(
% 3.62/1.04    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.04    inference(ennf_transformation,[],[f16])).
% 3.62/1.04  
% 3.62/1.04  fof(f58,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f34])).
% 3.62/1.04  
% 3.62/1.04  fof(f9,axiom,(
% 3.62/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f25,plain,(
% 3.62/1.04    ! [X0,X1] : (k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/1.04    inference(ennf_transformation,[],[f9])).
% 3.62/1.04  
% 3.62/1.04  fof(f50,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f25])).
% 3.62/1.04  
% 3.62/1.04  fof(f4,axiom,(
% 3.62/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f20,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.62/1.04    inference(ennf_transformation,[],[f4])).
% 3.62/1.04  
% 3.62/1.04  fof(f21,plain,(
% 3.62/1.04    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/1.04    inference(flattening,[],[f20])).
% 3.62/1.04  
% 3.62/1.04  fof(f45,plain,(
% 3.62/1.04    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/1.04    inference(cnf_transformation,[],[f21])).
% 3.62/1.04  
% 3.62/1.04  fof(f15,axiom,(
% 3.62/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.62/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.04  
% 3.62/1.04  fof(f33,plain,(
% 3.62/1.04    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.04    inference(ennf_transformation,[],[f15])).
% 3.62/1.04  
% 3.62/1.04  fof(f57,plain,(
% 3.62/1.04    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f33])).
% 3.62/1.04  
% 3.62/1.04  fof(f54,plain,(
% 3.62/1.04    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/1.04    inference(cnf_transformation,[],[f28])).
% 3.62/1.04  
% 3.62/1.04  fof(f63,plain,(
% 3.62/1.04    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.62/1.04    inference(cnf_transformation,[],[f41])).
% 3.62/1.04  
% 3.62/1.04  fof(f59,plain,(
% 3.62/1.04    v2_pre_topc(sK0)),
% 3.62/1.04    inference(cnf_transformation,[],[f41])).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3,plain,
% 3.62/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.62/1.04      inference(cnf_transformation,[],[f47]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_691,plain,
% 3.62/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2,plain,
% 3.62/1.04      ( k2_subset_1(X0) = X0 ),
% 3.62/1.04      inference(cnf_transformation,[],[f46]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_702,plain,
% 3.62/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.62/1.04      inference(light_normalisation,[status(thm)],[c_691,c_2]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_5,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.04      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.62/1.04      inference(cnf_transformation,[],[f67]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_689,plain,
% 3.62/1.04      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.62/1.04      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1266,plain,
% 3.62/1.04      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_702,c_689]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_16,negated_conjecture,
% 3.62/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.62/1.04      inference(cnf_transformation,[],[f61]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_678,plain,
% 3.62/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1265,plain,
% 3.62/1.04      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_678,c_689]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1707,plain,
% 3.62/1.04      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_1266,c_1265]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_15,negated_conjecture,
% 3.62/1.04      ( v4_pre_topc(sK1,sK0)
% 3.62/1.04      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/1.04      inference(cnf_transformation,[],[f62]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_679,plain,
% 3.62/1.04      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.62/1.04      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1717,plain,
% 3.62/1.04      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.62/1.04      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_1707,c_679]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_9,plain,
% 3.62/1.04      ( ~ v4_pre_topc(X0,X1)
% 3.62/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.04      | ~ l1_pre_topc(X1)
% 3.62/1.04      | k2_pre_topc(X1,X0) = X0 ),
% 3.62/1.04      inference(cnf_transformation,[],[f53]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_685,plain,
% 3.62/1.04      ( k2_pre_topc(X0,X1) = X1
% 3.62/1.04      | v4_pre_topc(X1,X0) != iProver_top
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.62/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2231,plain,
% 3.62/1.04      ( k2_pre_topc(sK0,sK1) = sK1
% 3.62/1.04      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.62/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_678,c_685]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_17,negated_conjecture,
% 3.62/1.04      ( l1_pre_topc(sK0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f60]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_20,plain,
% 3.62/1.04      ( l1_pre_topc(sK0) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2497,plain,
% 3.62/1.04      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.62/1.04      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/1.04      inference(global_propositional_subsumption,
% 3.62/1.04                [status(thm)],
% 3.62/1.04                [c_2231,c_20]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2498,plain,
% 3.62/1.04      ( k2_pre_topc(sK0,sK1) = sK1
% 3.62/1.04      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.62/1.04      inference(renaming,[status(thm)],[c_2497]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2820,plain,
% 3.62/1.04      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.62/1.04      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_1717,c_2498]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_0,plain,
% 3.62/1.04      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f65]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_693,plain,
% 3.62/1.04      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1706,plain,
% 3.62/1.04      ( r1_tarski(k7_subset_1(X0,X0,X1),X0) = iProver_top ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_1266,c_693]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3858,plain,
% 3.62/1.04      ( k2_pre_topc(sK0,sK1) = sK1
% 3.62/1.04      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_2820,c_1706]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_7,plain,
% 3.62/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/1.04      inference(cnf_transformation,[],[f52]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_687,plain,
% 3.62/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.62/1.04      | r1_tarski(X0,X1) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_4,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.62/1.04      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.62/1.04      inference(cnf_transformation,[],[f66]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_690,plain,
% 3.62/1.04      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.62/1.04      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1995,plain,
% 3.62/1.04      ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_702,c_690]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_4155,plain,
% 3.62/1.04      ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 3.62/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_687,c_1995]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_5306,plain,
% 3.62/1.04      ( k2_pre_topc(sK0,sK1) = sK1
% 3.62/1.04      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3858,c_4155]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_10,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.04      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.04      | ~ l1_pre_topc(X1) ),
% 3.62/1.04      inference(cnf_transformation,[],[f55]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_684,plain,
% 3.62/1.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.62/1.04      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.62/1.04      | l1_pre_topc(X1) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1994,plain,
% 3.62/1.04      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 3.62/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_678,c_690]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2631,plain,
% 3.62/1.04      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.62/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.62/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_684,c_1994]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3571,plain,
% 3.62/1.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.62/1.04      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 3.62/1.04      inference(global_propositional_subsumption,
% 3.62/1.04                [status(thm)],
% 3.62/1.04                [c_2631,c_20]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3572,plain,
% 3.62/1.04      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.62/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.62/1.04      inference(renaming,[status(thm)],[c_3571]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3581,plain,
% 3.62/1.04      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_678,c_3572]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_13,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.04      | ~ l1_pre_topc(X1)
% 3.62/1.04      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f58]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_681,plain,
% 3.62/1.04      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.62/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1151,plain,
% 3.62/1.04      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.62/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_678,c_681]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_954,plain,
% 3.62/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.62/1.04      | ~ l1_pre_topc(sK0)
% 3.62/1.04      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.62/1.04      inference(instantiation,[status(thm)],[c_13]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1527,plain,
% 3.62/1.04      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.62/1.04      inference(global_propositional_subsumption,
% 3.62/1.04                [status(thm)],
% 3.62/1.04                [c_1151,c_17,c_16,c_954]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_3586,plain,
% 3.62/1.04      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.62/1.04      inference(light_normalisation,[status(thm)],[c_3581,c_1527]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_5314,plain,
% 3.62/1.04      ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.62/1.04      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/1.04      inference(light_normalisation,[status(thm)],[c_5306,c_3586]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.04      | k4_subset_1(X1,X0,k2_subset_1(X1)) = k2_subset_1(X1) ),
% 3.62/1.04      inference(cnf_transformation,[],[f50]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_688,plain,
% 3.62/1.04      ( k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0)
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_711,plain,
% 3.62/1.04      ( k4_subset_1(X0,X1,X0) = X0
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/1.04      inference(light_normalisation,[status(thm)],[c_688,c_2]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1246,plain,
% 3.62/1.04      ( k4_subset_1(X0,X1,X0) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_687,c_711]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_5307,plain,
% 3.62/1.04      ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = sK1
% 3.62/1.04      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3858,c_1246]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.62/1.04      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f45]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_692,plain,
% 3.62/1.04      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.62/1.04      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2035,plain,
% 3.62/1.04      ( k4_subset_1(X0,X0,X1) = k4_subset_1(X0,X1,X0)
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_702,c_692]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_4917,plain,
% 3.62/1.04      ( k4_subset_1(X0,X0,X1) = k4_subset_1(X0,X1,X0)
% 3.62/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_687,c_2035]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_5305,plain,
% 3.62/1.04      ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
% 3.62/1.04      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_3858,c_4917]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_6865,plain,
% 3.62/1.04      ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = sK1
% 3.62/1.04      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_5307,c_5305]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_8655,plain,
% 3.62/1.04      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_5314,c_6865]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_12,plain,
% 3.62/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.04      | ~ l1_pre_topc(X1)
% 3.62/1.04      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f57]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_682,plain,
% 3.62/1.04      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.62/1.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.62/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.62/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_1835,plain,
% 3.62/1.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.62/1.04      | l1_pre_topc(sK0) != iProver_top ),
% 3.62/1.04      inference(superposition,[status(thm)],[c_678,c_682]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_960,plain,
% 3.62/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.62/1.04      | ~ l1_pre_topc(sK0)
% 3.62/1.04      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_2504,plain,
% 3.62/1.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/1.04      inference(global_propositional_subsumption,
% 3.62/1.04                [status(thm)],
% 3.62/1.04                [c_1835,c_17,c_16,c_960]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_9360,plain,
% 3.62/1.04      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.62/1.04      inference(demodulation,[status(thm)],[c_8655,c_2504]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_8,plain,
% 3.62/1.04      ( v4_pre_topc(X0,X1)
% 3.62/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.04      | ~ l1_pre_topc(X1)
% 3.62/1.04      | ~ v2_pre_topc(X1)
% 3.62/1.04      | k2_pre_topc(X1,X0) != X0 ),
% 3.62/1.04      inference(cnf_transformation,[],[f54]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_915,plain,
% 3.62/1.04      ( v4_pre_topc(sK1,sK0)
% 3.62/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.62/1.04      | ~ l1_pre_topc(sK0)
% 3.62/1.04      | ~ v2_pre_topc(sK0)
% 3.62/1.04      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.62/1.04      inference(instantiation,[status(thm)],[c_8]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_14,negated_conjecture,
% 3.62/1.04      ( ~ v4_pre_topc(sK1,sK0)
% 3.62/1.04      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.62/1.04      inference(cnf_transformation,[],[f63]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(c_18,negated_conjecture,
% 3.62/1.04      ( v2_pre_topc(sK0) ),
% 3.62/1.04      inference(cnf_transformation,[],[f59]) ).
% 3.62/1.04  
% 3.62/1.04  cnf(contradiction,plain,
% 3.62/1.04      ( $false ),
% 3.62/1.04      inference(minisat,
% 3.62/1.04                [status(thm)],
% 3.62/1.04                [c_9360,c_8655,c_915,c_14,c_16,c_17,c_18]) ).
% 3.62/1.04  
% 3.62/1.04  
% 3.62/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.04  
% 3.62/1.04  ------                               Statistics
% 3.62/1.04  
% 3.62/1.04  ------ Selected
% 3.62/1.04  
% 3.62/1.04  total_time:                             0.354
% 3.62/1.04  
%------------------------------------------------------------------------------

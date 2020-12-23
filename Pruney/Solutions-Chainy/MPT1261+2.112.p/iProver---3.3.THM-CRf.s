%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:40 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  161 (2362 expanded)
%              Number of clauses        :   95 ( 726 expanded)
%              Number of leaves         :   19 ( 502 expanded)
%              Depth                    :   24
%              Number of atoms          :  388 (9673 expanded)
%              Number of equality atoms :  199 (2956 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

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
    inference(nnf_transformation,[],[f39])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f66,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_721,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_725,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2062,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_725])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_923,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_924,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_2979,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2062,c_23,c_24,c_924])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_731,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_735,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1351,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_735])).

cnf(c_2985,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2979,c_1351])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3365,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_736])).

cnf(c_1133,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1134,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_5896,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_23,c_24,c_924,c_1134])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_734,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5901,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),X0) = k2_xboole_0(k1_tops_1(sK0,sK1),X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5896,c_734])).

cnf(c_7436,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,X0)) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_5901])).

cnf(c_24508,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_5896,c_7436])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_732,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_766,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_732,c_2])).

cnf(c_1524,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_766])).

cnf(c_2984,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2979,c_1524])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_737,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1903,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_737])).

cnf(c_3633,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2979,c_1903])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4182,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_3633,c_1])).

cnf(c_24515,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_24508,c_2984,c_4182])).

cnf(c_1904,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,X1))) = k3_subset_1(X0,k3_subset_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_737])).

cnf(c_13708,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) = k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_5896,c_1904])).

cnf(c_13715,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_13708,c_2985])).

cnf(c_14319,plain,
    ( k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_13715,c_1])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14626,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_14319,c_0])).

cnf(c_14631,plain,
    ( k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(light_normalisation,[status(thm)],[c_14626,c_4182])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_733,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2250,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_721,c_733])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_722,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2966,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2250,c_722])).

cnf(c_4170,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3633,c_2966])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_729,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2572,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_729])).

cnf(c_3207,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2572,c_23])).

cnf(c_3208,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3207])).

cnf(c_5683,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4170,c_3208])).

cnf(c_2249,plain,
    ( k5_xboole_0(k3_subset_1(X0,X1),k3_xboole_0(k3_subset_1(X0,X1),X2)) = k7_subset_1(X0,k3_subset_1(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_733])).

cnf(c_9491,plain,
    ( k5_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k3_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0)) = k7_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_5896,c_2249])).

cnf(c_10053,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_5683,c_9491])).

cnf(c_10066,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(X0,k7_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0)) = k2_xboole_0(X0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_10053,c_1])).

cnf(c_10055,plain,
    ( k2_xboole_0(X0,k7_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0)) = k2_xboole_0(X0,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_9491,c_1])).

cnf(c_11743,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(X0,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(X0,k2_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_10066,c_10055])).

cnf(c_11750,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0) = k2_xboole_0(X0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_11743,c_0])).

cnf(c_16036,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_14631,c_11750])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_728,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2529,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_734])).

cnf(c_3075,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_2529])).

cnf(c_5192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3075,c_23])).

cnf(c_5193,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5192])).

cnf(c_5203,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_721,c_5193])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_724,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1182,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_724])).

cnf(c_1003,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1702,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1182,c_20,c_19,c_1003])).

cnf(c_5205,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5203,c_1702])).

cnf(c_16039,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_16036,c_5205])).

cnf(c_24570,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_24515,c_16039])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_726,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3419,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_726])).

cnf(c_1006,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3752,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3419,c_20,c_19,c_1006])).

cnf(c_24607,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_24570,c_3752])).

cnf(c_10,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1000,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24607,c_24570,c_1000,c_17,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:56:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 22
% 7.75/1.50  conjectures                             5
% 7.75/1.50  EPR                                     2
% 7.75/1.50  Horn                                    21
% 7.75/1.50  unary                                   6
% 7.75/1.50  binary                                  8
% 7.75/1.50  lits                                    50
% 7.75/1.50  lits eq                                 14
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 0
% 7.75/1.50  fd_pseudo_cond                          0
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Input Options Time Limit: Unbounded
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f18,conjecture,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f19,negated_conjecture,(
% 7.75/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.75/1.50    inference(negated_conjecture,[],[f18])).
% 7.75/1.50  
% 7.75/1.50  fof(f38,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f19])).
% 7.75/1.50  
% 7.75/1.50  fof(f39,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f38])).
% 7.75/1.50  
% 7.75/1.50  fof(f40,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f39])).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f43,plain,(
% 7.75/1.50    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f42,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f44,plain,(
% 7.75/1.50    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 7.75/1.50  
% 7.75/1.50  fof(f65,plain,(
% 7.75/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.75/1.50    inference(cnf_transformation,[],[f44])).
% 7.75/1.50  
% 7.75/1.50  fof(f16,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f36,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f16])).
% 7.75/1.50  
% 7.75/1.50  fof(f61,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f36])).
% 7.75/1.50  
% 7.75/1.50  fof(f64,plain,(
% 7.75/1.50    l1_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f44])).
% 7.75/1.50  
% 7.75/1.50  fof(f11,axiom,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f20,plain,(
% 7.75/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.75/1.50    inference(unused_predicate_definition_removal,[],[f11])).
% 7.75/1.50  
% 7.75/1.50  fof(f28,plain,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.75/1.50    inference(ennf_transformation,[],[f20])).
% 7.75/1.50  
% 7.75/1.50  fof(f55,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f28])).
% 7.75/1.50  
% 7.75/1.50  fof(f7,axiom,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f23,plain,(
% 7.75/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f7])).
% 7.75/1.50  
% 7.75/1.50  fof(f51,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f23])).
% 7.75/1.50  
% 7.75/1.50  fof(f6,axiom,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f22,plain,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f6])).
% 7.75/1.50  
% 7.75/1.50  fof(f50,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f22])).
% 7.75/1.50  
% 7.75/1.50  fof(f8,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f24,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.75/1.50    inference(ennf_transformation,[],[f8])).
% 7.75/1.50  
% 7.75/1.50  fof(f25,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.50    inference(flattening,[],[f24])).
% 7.75/1.50  
% 7.75/1.50  fof(f52,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f10,axiom,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f27,plain,(
% 7.75/1.50    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f10])).
% 7.75/1.50  
% 7.75/1.50  fof(f54,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f4,axiom,(
% 7.75/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f48,plain,(
% 7.75/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.75/1.50    inference(cnf_transformation,[],[f4])).
% 7.75/1.50  
% 7.75/1.50  fof(f5,axiom,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f21,plain,(
% 7.75/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f5])).
% 7.75/1.50  
% 7.75/1.50  fof(f49,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f21])).
% 7.75/1.50  
% 7.75/1.50  fof(f2,axiom,(
% 7.75/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f46,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f2])).
% 7.75/1.50  
% 7.75/1.50  fof(f69,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(definition_unfolding,[],[f49,f46])).
% 7.75/1.50  
% 7.75/1.50  fof(f3,axiom,(
% 7.75/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f47,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f3])).
% 7.75/1.50  
% 7.75/1.50  fof(f68,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.75/1.50    inference(definition_unfolding,[],[f47,f46])).
% 7.75/1.50  
% 7.75/1.50  fof(f1,axiom,(
% 7.75/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f45,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f1])).
% 7.75/1.50  
% 7.75/1.50  fof(f9,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f26,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f9])).
% 7.75/1.50  
% 7.75/1.50  fof(f53,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f26])).
% 7.75/1.50  
% 7.75/1.50  fof(f70,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(definition_unfolding,[],[f53,f46])).
% 7.75/1.50  
% 7.75/1.50  fof(f66,plain,(
% 7.75/1.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f44])).
% 7.75/1.50  
% 7.75/1.50  fof(f12,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f29,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f12])).
% 7.75/1.50  
% 7.75/1.50  fof(f30,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f29])).
% 7.75/1.50  
% 7.75/1.50  fof(f56,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f30])).
% 7.75/1.50  
% 7.75/1.50  fof(f13,axiom,(
% 7.75/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f31,plain,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f13])).
% 7.75/1.50  
% 7.75/1.50  fof(f32,plain,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f31])).
% 7.75/1.50  
% 7.75/1.50  fof(f58,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f32])).
% 7.75/1.50  
% 7.75/1.50  fof(f17,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f37,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f17])).
% 7.75/1.50  
% 7.75/1.50  fof(f62,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f37])).
% 7.75/1.50  
% 7.75/1.50  fof(f15,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f35,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f15])).
% 7.75/1.50  
% 7.75/1.50  fof(f60,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f35])).
% 7.75/1.50  
% 7.75/1.50  fof(f57,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f30])).
% 7.75/1.50  
% 7.75/1.50  fof(f67,plain,(
% 7.75/1.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f44])).
% 7.75/1.50  
% 7.75/1.50  fof(f63,plain,(
% 7.75/1.50    v2_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f44])).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19,negated_conjecture,
% 7.75/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.75/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_721,plain,
% 7.75/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_15,plain,
% 7.75/1.50      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 7.75/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.75/1.50      | ~ l1_pre_topc(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_725,plain,
% 7.75/1.50      ( r1_tarski(k1_tops_1(X0,X1),X1) = iProver_top
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2062,plain,
% 7.75/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_721,c_725]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20,negated_conjecture,
% 7.75/1.50      ( l1_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23,plain,
% 7.75/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24,plain,
% 7.75/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_923,plain,
% 7.75/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 7.75/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | ~ l1_pre_topc(sK0) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_924,plain,
% 7.75/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 7.75/1.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_923]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2979,plain,
% 7.75/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_2062,c_23,c_24,c_924]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_731,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_735,plain,
% 7.75/1.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1351,plain,
% 7.75/1.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.75/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_731,c_735]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2985,plain,
% 7.75/1.50      ( k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2979,c_1351]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_736,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.75/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3365,plain,
% 7.75/1.50      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top
% 7.75/1.50      | m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2985,c_736]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1133,plain,
% 7.75/1.50      ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 7.75/1.50      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1134,plain,
% 7.75/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 7.75/1.50      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5896,plain,
% 7.75/1.50      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_3365,c_23,c_24,c_924,c_1134]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.75/1.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.75/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_734,plain,
% 7.75/1.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5901,plain,
% 7.75/1.50      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),X0) = k2_xboole_0(k1_tops_1(sK0,sK1),X0)
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5896,c_734]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7436,plain,
% 7.75/1.50      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,X0)) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,X0))
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_736,c_5901]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24508,plain,
% 7.75/1.50      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5896,c_7436]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_8,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_732,plain,
% 7.75/1.50      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2,plain,
% 7.75/1.50      ( k2_subset_1(X0) = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_766,plain,
% 7.75/1.50      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_732,c_2]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1524,plain,
% 7.75/1.50      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 7.75/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_731,c_766]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2984,plain,
% 7.75/1.50      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2979,c_1524]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_737,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1903,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.75/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_731,c_737]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3633,plain,
% 7.75/1.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2979,c_1903]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1,plain,
% 7.75/1.50      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4182,plain,
% 7.75/1.50      ( k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3633,c_1]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24515,plain,
% 7.75/1.50      ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
% 7.75/1.50      inference(light_normalisation,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_24508,c_2984,c_4182]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1904,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,X1))) = k3_subset_1(X0,k3_subset_1(X0,X1))
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_736,c_737]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_13708,plain,
% 7.75/1.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) = k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5896,c_1904]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_13715,plain,
% 7.75/1.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_13708,c_2985]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14319,plain,
% 7.75/1.50      ( k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_13715,c_1]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_0,plain,
% 7.75/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14626,plain,
% 7.75/1.50      ( k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_14319,c_0]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14631,plain,
% 7.75/1.50      ( k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_14626,c_4182]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.75/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_733,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2250,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_721,c_733]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18,negated_conjecture,
% 7.75/1.50      ( v4_pre_topc(sK1,sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_722,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2966,plain,
% 7.75/1.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_2250,c_722]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4170,plain,
% 7.75/1.50      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_3633,c_2966]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_11,plain,
% 7.75/1.50      ( ~ v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | k2_pre_topc(X1,X0) = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_729,plain,
% 7.75/1.50      ( k2_pre_topc(X0,X1) = X1
% 7.75/1.50      | v4_pre_topc(X1,X0) != iProver_top
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2572,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_721,c_729]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3207,plain,
% 7.75/1.50      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.75/1.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_2572,c_23]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3208,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_3207]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5683,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_4170,c_3208]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2249,plain,
% 7.75/1.50      ( k5_xboole_0(k3_subset_1(X0,X1),k3_xboole_0(k3_subset_1(X0,X1),X2)) = k7_subset_1(X0,k3_subset_1(X0,X1),X2)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_736,c_733]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9491,plain,
% 7.75/1.50      ( k5_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k3_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0)) = k7_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5896,c_2249]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10053,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5683,c_9491]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10066,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k2_xboole_0(X0,k7_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0)) = k2_xboole_0(X0,k2_tops_1(sK0,sK1)) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_10053,c_1]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10055,plain,
% 7.75/1.50      ( k2_xboole_0(X0,k7_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0)) = k2_xboole_0(X0,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_9491,c_1]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_11743,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k2_xboole_0(X0,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(X0,k2_tops_1(sK0,sK1)) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_10066,c_10055]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_11750,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),X0) = k2_xboole_0(X0,k2_tops_1(sK0,sK1)) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_11743,c_0]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16036,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_14631,c_11750]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_12,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_728,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.75/1.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.75/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2529,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_721,c_734]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3075,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_728,c_2529]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5192,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_3075,c_23]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5193,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_5192]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5203,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_721,c_5193]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_724,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1182,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_721,c_724]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1003,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1702,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_1182,c_20,c_19,c_1003]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5205,plain,
% 7.75/1.50      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_5203,c_1702]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16039,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_16036,c_5205]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24570,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_24515,c_16039]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_726,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3419,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_721,c_726]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1006,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3752,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_3419,c_20,c_19,c_1006]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24607,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_24570,c_3752]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10,plain,
% 7.75/1.50      ( v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | k2_pre_topc(X1,X0) != X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1000,plain,
% 7.75/1.50      ( v4_pre_topc(sK1,sK0)
% 7.75/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | ~ v2_pre_topc(sK0)
% 7.75/1.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17,negated_conjecture,
% 7.75/1.50      ( ~ v4_pre_topc(sK1,sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21,negated_conjecture,
% 7.75/1.50      ( v2_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(contradiction,plain,
% 7.75/1.50      ( $false ),
% 7.75/1.50      inference(minisat,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_24607,c_24570,c_1000,c_17,c_19,c_20,c_21]) ).
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  ------                               Statistics
% 7.75/1.50  
% 7.75/1.50  ------ Selected
% 7.75/1.50  
% 7.75/1.50  total_time:                             0.795
% 7.75/1.50  
%------------------------------------------------------------------------------

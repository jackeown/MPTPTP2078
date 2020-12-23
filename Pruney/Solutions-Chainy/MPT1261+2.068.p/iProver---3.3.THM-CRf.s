%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:34 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 618 expanded)
%              Number of clauses        :   65 ( 159 expanded)
%              Number of leaves         :   15 ( 144 expanded)
%              Depth                    :   20
%              Number of atoms          :  316 (2613 expanded)
%              Number of equality atoms :  146 ( 872 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f39,f39])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f54,f54])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_120,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_304,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_305,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_120,c_305])).

cnf(c_352,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_354,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_14])).

cnf(c_441,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_354])).

cnf(c_442,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_821,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_822,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1786,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_821,c_822])).

cnf(c_1854,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_442,c_1786])).

cnf(c_3,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_825,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_824,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_842,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_824,c_1])).

cnf(c_1290,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_825,c_842])).

cnf(c_2514,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_1290])).

cnf(c_3594,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_1854,c_2514])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_818,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k2_enumset1(X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_823,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1803,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k2_tops_1(sK0,X1))) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_823])).

cnf(c_3049,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_1803])).

cnf(c_3187,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_821,c_3049])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_820,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_938,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_821,c_820])).

cnf(c_1802,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_823])).

cnf(c_1860,plain,
    ( k3_tarski(k2_enumset1(k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_1802])).

cnf(c_2731,plain,
    ( k3_tarski(k2_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_821,c_1860])).

cnf(c_2743,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_3,c_2731])).

cnf(c_3194,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3187,c_938,c_2743])).

cnf(c_3615,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_3594,c_3194])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_819,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_996,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_821,c_819])).

cnf(c_3729,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3615,c_996])).

cnf(c_12,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_118,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_240,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_241,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_241,c_15])).

cnf(c_246,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_245])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_118,c_246])).

cnf(c_363,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_365,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3729,c_3615,c_365])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:32:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.17/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/0.92  
% 2.17/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.92  
% 2.17/0.92  ------  iProver source info
% 2.17/0.92  
% 2.17/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.92  git: non_committed_changes: false
% 2.17/0.92  git: last_make_outside_of_git: false
% 2.17/0.92  
% 2.17/0.92  ------ 
% 2.17/0.92  
% 2.17/0.92  ------ Input Options
% 2.17/0.92  
% 2.17/0.92  --out_options                           all
% 2.17/0.92  --tptp_safe_out                         true
% 2.17/0.92  --problem_path                          ""
% 2.17/0.92  --include_path                          ""
% 2.17/0.92  --clausifier                            res/vclausify_rel
% 2.17/0.92  --clausifier_options                    --mode clausify
% 2.17/0.92  --stdin                                 false
% 2.17/0.92  --stats_out                             all
% 2.17/0.92  
% 2.17/0.92  ------ General Options
% 2.17/0.92  
% 2.17/0.92  --fof                                   false
% 2.17/0.92  --time_out_real                         305.
% 2.17/0.92  --time_out_virtual                      -1.
% 2.17/0.92  --symbol_type_check                     false
% 2.17/0.92  --clausify_out                          false
% 2.17/0.92  --sig_cnt_out                           false
% 2.17/0.92  --trig_cnt_out                          false
% 2.17/0.92  --trig_cnt_out_tolerance                1.
% 2.17/0.92  --trig_cnt_out_sk_spl                   false
% 2.17/0.92  --abstr_cl_out                          false
% 2.17/0.92  
% 2.17/0.92  ------ Global Options
% 2.17/0.92  
% 2.17/0.92  --schedule                              default
% 2.17/0.92  --add_important_lit                     false
% 2.17/0.92  --prop_solver_per_cl                    1000
% 2.17/0.92  --min_unsat_core                        false
% 2.17/0.92  --soft_assumptions                      false
% 2.17/0.92  --soft_lemma_size                       3
% 2.17/0.92  --prop_impl_unit_size                   0
% 2.17/0.92  --prop_impl_unit                        []
% 2.17/0.92  --share_sel_clauses                     true
% 2.17/0.92  --reset_solvers                         false
% 2.17/0.92  --bc_imp_inh                            [conj_cone]
% 2.17/0.92  --conj_cone_tolerance                   3.
% 2.17/0.92  --extra_neg_conj                        none
% 2.17/0.92  --large_theory_mode                     true
% 2.17/0.92  --prolific_symb_bound                   200
% 2.17/0.92  --lt_threshold                          2000
% 2.17/0.92  --clause_weak_htbl                      true
% 2.17/0.92  --gc_record_bc_elim                     false
% 2.17/0.92  
% 2.17/0.92  ------ Preprocessing Options
% 2.17/0.92  
% 2.17/0.92  --preprocessing_flag                    true
% 2.17/0.92  --time_out_prep_mult                    0.1
% 2.17/0.92  --splitting_mode                        input
% 2.17/0.92  --splitting_grd                         true
% 2.17/0.92  --splitting_cvd                         false
% 2.17/0.92  --splitting_cvd_svl                     false
% 2.17/0.92  --splitting_nvd                         32
% 2.17/0.92  --sub_typing                            true
% 2.17/0.92  --prep_gs_sim                           true
% 2.17/0.92  --prep_unflatten                        true
% 2.17/0.92  --prep_res_sim                          true
% 2.17/0.92  --prep_upred                            true
% 2.17/0.92  --prep_sem_filter                       exhaustive
% 2.17/0.92  --prep_sem_filter_out                   false
% 2.17/0.92  --pred_elim                             true
% 2.17/0.92  --res_sim_input                         true
% 2.17/0.92  --eq_ax_congr_red                       true
% 2.17/0.92  --pure_diseq_elim                       true
% 2.17/0.92  --brand_transform                       false
% 2.17/0.92  --non_eq_to_eq                          false
% 2.17/0.92  --prep_def_merge                        true
% 2.17/0.92  --prep_def_merge_prop_impl              false
% 2.17/0.92  --prep_def_merge_mbd                    true
% 2.17/0.92  --prep_def_merge_tr_red                 false
% 2.17/0.92  --prep_def_merge_tr_cl                  false
% 2.17/0.92  --smt_preprocessing                     true
% 2.17/0.92  --smt_ac_axioms                         fast
% 2.17/0.92  --preprocessed_out                      false
% 2.17/0.92  --preprocessed_stats                    false
% 2.17/0.92  
% 2.17/0.92  ------ Abstraction refinement Options
% 2.17/0.92  
% 2.17/0.92  --abstr_ref                             []
% 2.17/0.92  --abstr_ref_prep                        false
% 2.17/0.92  --abstr_ref_until_sat                   false
% 2.17/0.92  --abstr_ref_sig_restrict                funpre
% 2.17/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.92  --abstr_ref_under                       []
% 2.17/0.92  
% 2.17/0.92  ------ SAT Options
% 2.17/0.92  
% 2.17/0.92  --sat_mode                              false
% 2.17/0.92  --sat_fm_restart_options                ""
% 2.17/0.92  --sat_gr_def                            false
% 2.17/0.92  --sat_epr_types                         true
% 2.17/0.92  --sat_non_cyclic_types                  false
% 2.17/0.92  --sat_finite_models                     false
% 2.17/0.92  --sat_fm_lemmas                         false
% 2.17/0.92  --sat_fm_prep                           false
% 2.17/0.92  --sat_fm_uc_incr                        true
% 2.17/0.92  --sat_out_model                         small
% 2.17/0.92  --sat_out_clauses                       false
% 2.17/0.92  
% 2.17/0.92  ------ QBF Options
% 2.17/0.92  
% 2.17/0.92  --qbf_mode                              false
% 2.17/0.92  --qbf_elim_univ                         false
% 2.17/0.92  --qbf_dom_inst                          none
% 2.17/0.92  --qbf_dom_pre_inst                      false
% 2.17/0.92  --qbf_sk_in                             false
% 2.17/0.92  --qbf_pred_elim                         true
% 2.17/0.92  --qbf_split                             512
% 2.17/0.92  
% 2.17/0.92  ------ BMC1 Options
% 2.17/0.92  
% 2.17/0.92  --bmc1_incremental                      false
% 2.17/0.92  --bmc1_axioms                           reachable_all
% 2.17/0.92  --bmc1_min_bound                        0
% 2.17/0.92  --bmc1_max_bound                        -1
% 2.17/0.92  --bmc1_max_bound_default                -1
% 2.17/0.92  --bmc1_symbol_reachability              true
% 2.17/0.92  --bmc1_property_lemmas                  false
% 2.17/0.92  --bmc1_k_induction                      false
% 2.17/0.92  --bmc1_non_equiv_states                 false
% 2.17/0.92  --bmc1_deadlock                         false
% 2.17/0.92  --bmc1_ucm                              false
% 2.17/0.92  --bmc1_add_unsat_core                   none
% 2.17/0.92  --bmc1_unsat_core_children              false
% 2.17/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.92  --bmc1_out_stat                         full
% 2.17/0.92  --bmc1_ground_init                      false
% 2.17/0.92  --bmc1_pre_inst_next_state              false
% 2.17/0.92  --bmc1_pre_inst_state                   false
% 2.17/0.92  --bmc1_pre_inst_reach_state             false
% 2.17/0.92  --bmc1_out_unsat_core                   false
% 2.17/0.92  --bmc1_aig_witness_out                  false
% 2.17/0.92  --bmc1_verbose                          false
% 2.17/0.92  --bmc1_dump_clauses_tptp                false
% 2.17/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.92  --bmc1_dump_file                        -
% 2.17/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.92  --bmc1_ucm_extend_mode                  1
% 2.17/0.92  --bmc1_ucm_init_mode                    2
% 2.17/0.92  --bmc1_ucm_cone_mode                    none
% 2.17/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.92  --bmc1_ucm_relax_model                  4
% 2.17/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.92  --bmc1_ucm_layered_model                none
% 2.17/0.92  --bmc1_ucm_max_lemma_size               10
% 2.17/0.92  
% 2.17/0.92  ------ AIG Options
% 2.17/0.92  
% 2.17/0.92  --aig_mode                              false
% 2.17/0.92  
% 2.17/0.92  ------ Instantiation Options
% 2.17/0.92  
% 2.17/0.92  --instantiation_flag                    true
% 2.17/0.92  --inst_sos_flag                         false
% 2.17/0.92  --inst_sos_phase                        true
% 2.17/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.92  --inst_lit_sel_side                     num_symb
% 2.17/0.92  --inst_solver_per_active                1400
% 2.17/0.92  --inst_solver_calls_frac                1.
% 2.17/0.92  --inst_passive_queue_type               priority_queues
% 2.17/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.92  --inst_passive_queues_freq              [25;2]
% 2.17/0.92  --inst_dismatching                      true
% 2.17/0.92  --inst_eager_unprocessed_to_passive     true
% 2.17/0.92  --inst_prop_sim_given                   true
% 2.17/0.92  --inst_prop_sim_new                     false
% 2.17/0.92  --inst_subs_new                         false
% 2.17/0.92  --inst_eq_res_simp                      false
% 2.17/0.92  --inst_subs_given                       false
% 2.17/0.92  --inst_orphan_elimination               true
% 2.17/0.92  --inst_learning_loop_flag               true
% 2.17/0.92  --inst_learning_start                   3000
% 2.17/0.92  --inst_learning_factor                  2
% 2.17/0.92  --inst_start_prop_sim_after_learn       3
% 2.17/0.92  --inst_sel_renew                        solver
% 2.17/0.92  --inst_lit_activity_flag                true
% 2.17/0.92  --inst_restr_to_given                   false
% 2.17/0.92  --inst_activity_threshold               500
% 2.17/0.92  --inst_out_proof                        true
% 2.17/0.92  
% 2.17/0.92  ------ Resolution Options
% 2.17/0.92  
% 2.17/0.92  --resolution_flag                       true
% 2.17/0.92  --res_lit_sel                           adaptive
% 2.17/0.92  --res_lit_sel_side                      none
% 2.17/0.92  --res_ordering                          kbo
% 2.17/0.92  --res_to_prop_solver                    active
% 2.17/0.92  --res_prop_simpl_new                    false
% 2.17/0.92  --res_prop_simpl_given                  true
% 2.17/0.92  --res_passive_queue_type                priority_queues
% 2.17/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.92  --res_passive_queues_freq               [15;5]
% 2.17/0.92  --res_forward_subs                      full
% 2.17/0.92  --res_backward_subs                     full
% 2.17/0.92  --res_forward_subs_resolution           true
% 2.17/0.92  --res_backward_subs_resolution          true
% 2.17/0.92  --res_orphan_elimination                true
% 2.17/0.92  --res_time_limit                        2.
% 2.17/0.92  --res_out_proof                         true
% 2.17/0.92  
% 2.17/0.92  ------ Superposition Options
% 2.17/0.92  
% 2.17/0.92  --superposition_flag                    true
% 2.17/0.92  --sup_passive_queue_type                priority_queues
% 2.17/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.92  --demod_completeness_check              fast
% 2.17/0.92  --demod_use_ground                      true
% 2.17/0.92  --sup_to_prop_solver                    passive
% 2.17/0.92  --sup_prop_simpl_new                    true
% 2.17/0.92  --sup_prop_simpl_given                  true
% 2.17/0.92  --sup_fun_splitting                     false
% 2.17/0.92  --sup_smt_interval                      50000
% 2.17/0.92  
% 2.17/0.92  ------ Superposition Simplification Setup
% 2.17/0.92  
% 2.17/0.92  --sup_indices_passive                   []
% 2.17/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.92  --sup_full_bw                           [BwDemod]
% 2.17/0.92  --sup_immed_triv                        [TrivRules]
% 2.17/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.92  --sup_immed_bw_main                     []
% 2.17/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.92  
% 2.17/0.92  ------ Combination Options
% 2.17/0.92  
% 2.17/0.92  --comb_res_mult                         3
% 2.17/0.92  --comb_sup_mult                         2
% 2.17/0.92  --comb_inst_mult                        10
% 2.17/0.92  
% 2.17/0.92  ------ Debug Options
% 2.17/0.92  
% 2.17/0.92  --dbg_backtrace                         false
% 2.17/0.92  --dbg_dump_prop_clauses                 false
% 2.17/0.92  --dbg_dump_prop_clauses_file            -
% 2.17/0.92  --dbg_out_stat                          false
% 2.17/0.92  ------ Parsing...
% 2.17/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.92  
% 2.17/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.17/0.92  
% 2.17/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.92  
% 2.17/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.92  ------ Proving...
% 2.17/0.92  ------ Problem Properties 
% 2.17/0.92  
% 2.17/0.92  
% 2.17/0.92  clauses                                 14
% 2.17/0.92  conjectures                             1
% 2.17/0.92  EPR                                     0
% 2.17/0.92  Horn                                    13
% 2.17/0.92  unary                                   4
% 2.17/0.92  binary                                  7
% 2.17/0.92  lits                                    27
% 2.17/0.92  lits eq                                 14
% 2.17/0.92  fd_pure                                 0
% 2.17/0.92  fd_pseudo                               0
% 2.17/0.92  fd_cond                                 0
% 2.17/0.92  fd_pseudo_cond                          0
% 2.17/0.92  AC symbols                              0
% 2.17/0.92  
% 2.17/0.92  ------ Schedule dynamic 5 is on 
% 2.17/0.92  
% 2.17/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/0.92  
% 2.17/0.92  
% 2.17/0.92  ------ 
% 2.17/0.92  Current options:
% 2.17/0.92  ------ 
% 2.17/0.92  
% 2.17/0.92  ------ Input Options
% 2.17/0.92  
% 2.17/0.92  --out_options                           all
% 2.17/0.92  --tptp_safe_out                         true
% 2.17/0.92  --problem_path                          ""
% 2.17/0.92  --include_path                          ""
% 2.17/0.92  --clausifier                            res/vclausify_rel
% 2.17/0.92  --clausifier_options                    --mode clausify
% 2.17/0.92  --stdin                                 false
% 2.17/0.92  --stats_out                             all
% 2.17/0.92  
% 2.17/0.92  ------ General Options
% 2.17/0.92  
% 2.17/0.92  --fof                                   false
% 2.17/0.92  --time_out_real                         305.
% 2.17/0.92  --time_out_virtual                      -1.
% 2.17/0.92  --symbol_type_check                     false
% 2.17/0.92  --clausify_out                          false
% 2.17/0.92  --sig_cnt_out                           false
% 2.17/0.92  --trig_cnt_out                          false
% 2.17/0.92  --trig_cnt_out_tolerance                1.
% 2.17/0.92  --trig_cnt_out_sk_spl                   false
% 2.17/0.92  --abstr_cl_out                          false
% 2.17/0.92  
% 2.17/0.92  ------ Global Options
% 2.17/0.92  
% 2.17/0.92  --schedule                              default
% 2.17/0.92  --add_important_lit                     false
% 2.17/0.92  --prop_solver_per_cl                    1000
% 2.17/0.92  --min_unsat_core                        false
% 2.17/0.92  --soft_assumptions                      false
% 2.17/0.92  --soft_lemma_size                       3
% 2.17/0.92  --prop_impl_unit_size                   0
% 2.17/0.92  --prop_impl_unit                        []
% 2.17/0.92  --share_sel_clauses                     true
% 2.17/0.92  --reset_solvers                         false
% 2.17/0.92  --bc_imp_inh                            [conj_cone]
% 2.17/0.92  --conj_cone_tolerance                   3.
% 2.17/0.92  --extra_neg_conj                        none
% 2.17/0.92  --large_theory_mode                     true
% 2.17/0.92  --prolific_symb_bound                   200
% 2.17/0.92  --lt_threshold                          2000
% 2.17/0.92  --clause_weak_htbl                      true
% 2.17/0.92  --gc_record_bc_elim                     false
% 2.17/0.92  
% 2.17/0.92  ------ Preprocessing Options
% 2.17/0.92  
% 2.17/0.92  --preprocessing_flag                    true
% 2.17/0.92  --time_out_prep_mult                    0.1
% 2.17/0.92  --splitting_mode                        input
% 2.17/0.92  --splitting_grd                         true
% 2.17/0.92  --splitting_cvd                         false
% 2.17/0.92  --splitting_cvd_svl                     false
% 2.17/0.92  --splitting_nvd                         32
% 2.17/0.92  --sub_typing                            true
% 2.17/0.92  --prep_gs_sim                           true
% 2.17/0.92  --prep_unflatten                        true
% 2.17/0.92  --prep_res_sim                          true
% 2.17/0.92  --prep_upred                            true
% 2.17/0.92  --prep_sem_filter                       exhaustive
% 2.17/0.92  --prep_sem_filter_out                   false
% 2.17/0.92  --pred_elim                             true
% 2.17/0.92  --res_sim_input                         true
% 2.17/0.92  --eq_ax_congr_red                       true
% 2.17/0.92  --pure_diseq_elim                       true
% 2.17/0.92  --brand_transform                       false
% 2.17/0.92  --non_eq_to_eq                          false
% 2.17/0.92  --prep_def_merge                        true
% 2.17/0.92  --prep_def_merge_prop_impl              false
% 2.17/0.92  --prep_def_merge_mbd                    true
% 2.17/0.92  --prep_def_merge_tr_red                 false
% 2.17/0.92  --prep_def_merge_tr_cl                  false
% 2.17/0.92  --smt_preprocessing                     true
% 2.17/0.92  --smt_ac_axioms                         fast
% 2.17/0.92  --preprocessed_out                      false
% 2.17/0.92  --preprocessed_stats                    false
% 2.17/0.92  
% 2.17/0.92  ------ Abstraction refinement Options
% 2.17/0.92  
% 2.17/0.92  --abstr_ref                             []
% 2.17/0.92  --abstr_ref_prep                        false
% 2.17/0.92  --abstr_ref_until_sat                   false
% 2.17/0.92  --abstr_ref_sig_restrict                funpre
% 2.17/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.92  --abstr_ref_under                       []
% 2.17/0.92  
% 2.17/0.92  ------ SAT Options
% 2.17/0.92  
% 2.17/0.92  --sat_mode                              false
% 2.17/0.92  --sat_fm_restart_options                ""
% 2.17/0.92  --sat_gr_def                            false
% 2.17/0.92  --sat_epr_types                         true
% 2.17/0.92  --sat_non_cyclic_types                  false
% 2.17/0.92  --sat_finite_models                     false
% 2.17/0.92  --sat_fm_lemmas                         false
% 2.17/0.92  --sat_fm_prep                           false
% 2.17/0.92  --sat_fm_uc_incr                        true
% 2.17/0.92  --sat_out_model                         small
% 2.17/0.92  --sat_out_clauses                       false
% 2.17/0.92  
% 2.17/0.92  ------ QBF Options
% 2.17/0.92  
% 2.17/0.92  --qbf_mode                              false
% 2.17/0.92  --qbf_elim_univ                         false
% 2.17/0.92  --qbf_dom_inst                          none
% 2.17/0.92  --qbf_dom_pre_inst                      false
% 2.17/0.92  --qbf_sk_in                             false
% 2.17/0.92  --qbf_pred_elim                         true
% 2.17/0.92  --qbf_split                             512
% 2.17/0.92  
% 2.17/0.92  ------ BMC1 Options
% 2.17/0.92  
% 2.17/0.92  --bmc1_incremental                      false
% 2.17/0.92  --bmc1_axioms                           reachable_all
% 2.17/0.92  --bmc1_min_bound                        0
% 2.17/0.92  --bmc1_max_bound                        -1
% 2.17/0.92  --bmc1_max_bound_default                -1
% 2.17/0.92  --bmc1_symbol_reachability              true
% 2.17/0.92  --bmc1_property_lemmas                  false
% 2.17/0.92  --bmc1_k_induction                      false
% 2.17/0.92  --bmc1_non_equiv_states                 false
% 2.17/0.92  --bmc1_deadlock                         false
% 2.17/0.92  --bmc1_ucm                              false
% 2.17/0.92  --bmc1_add_unsat_core                   none
% 2.17/0.92  --bmc1_unsat_core_children              false
% 2.17/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.92  --bmc1_out_stat                         full
% 2.17/0.92  --bmc1_ground_init                      false
% 2.17/0.92  --bmc1_pre_inst_next_state              false
% 2.17/0.92  --bmc1_pre_inst_state                   false
% 2.17/0.92  --bmc1_pre_inst_reach_state             false
% 2.17/0.92  --bmc1_out_unsat_core                   false
% 2.17/0.92  --bmc1_aig_witness_out                  false
% 2.17/0.92  --bmc1_verbose                          false
% 2.17/0.92  --bmc1_dump_clauses_tptp                false
% 2.17/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.92  --bmc1_dump_file                        -
% 2.17/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.92  --bmc1_ucm_extend_mode                  1
% 2.17/0.92  --bmc1_ucm_init_mode                    2
% 2.17/0.92  --bmc1_ucm_cone_mode                    none
% 2.17/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.92  --bmc1_ucm_relax_model                  4
% 2.17/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.92  --bmc1_ucm_layered_model                none
% 2.17/0.92  --bmc1_ucm_max_lemma_size               10
% 2.17/0.92  
% 2.17/0.92  ------ AIG Options
% 2.17/0.92  
% 2.17/0.92  --aig_mode                              false
% 2.17/0.92  
% 2.17/0.92  ------ Instantiation Options
% 2.17/0.92  
% 2.17/0.92  --instantiation_flag                    true
% 2.17/0.92  --inst_sos_flag                         false
% 2.17/0.92  --inst_sos_phase                        true
% 2.17/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.92  --inst_lit_sel_side                     none
% 2.17/0.92  --inst_solver_per_active                1400
% 2.17/0.92  --inst_solver_calls_frac                1.
% 2.17/0.92  --inst_passive_queue_type               priority_queues
% 2.17/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.92  --inst_passive_queues_freq              [25;2]
% 2.17/0.92  --inst_dismatching                      true
% 2.17/0.92  --inst_eager_unprocessed_to_passive     true
% 2.17/0.92  --inst_prop_sim_given                   true
% 2.17/0.92  --inst_prop_sim_new                     false
% 2.17/0.92  --inst_subs_new                         false
% 2.17/0.92  --inst_eq_res_simp                      false
% 2.17/0.92  --inst_subs_given                       false
% 2.17/0.92  --inst_orphan_elimination               true
% 2.17/0.92  --inst_learning_loop_flag               true
% 2.17/0.92  --inst_learning_start                   3000
% 2.17/0.92  --inst_learning_factor                  2
% 2.17/0.92  --inst_start_prop_sim_after_learn       3
% 2.17/0.92  --inst_sel_renew                        solver
% 2.17/0.92  --inst_lit_activity_flag                true
% 2.17/0.92  --inst_restr_to_given                   false
% 2.17/0.92  --inst_activity_threshold               500
% 2.17/0.92  --inst_out_proof                        true
% 2.17/0.92  
% 2.17/0.92  ------ Resolution Options
% 2.17/0.92  
% 2.17/0.92  --resolution_flag                       false
% 2.17/0.92  --res_lit_sel                           adaptive
% 2.17/0.92  --res_lit_sel_side                      none
% 2.17/0.92  --res_ordering                          kbo
% 2.17/0.92  --res_to_prop_solver                    active
% 2.17/0.92  --res_prop_simpl_new                    false
% 2.17/0.92  --res_prop_simpl_given                  true
% 2.17/0.92  --res_passive_queue_type                priority_queues
% 2.17/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.92  --res_passive_queues_freq               [15;5]
% 2.17/0.92  --res_forward_subs                      full
% 2.17/0.92  --res_backward_subs                     full
% 2.17/0.92  --res_forward_subs_resolution           true
% 2.17/0.92  --res_backward_subs_resolution          true
% 2.17/0.92  --res_orphan_elimination                true
% 2.17/0.92  --res_time_limit                        2.
% 2.17/0.92  --res_out_proof                         true
% 2.17/0.92  
% 2.17/0.92  ------ Superposition Options
% 2.17/0.92  
% 2.17/0.92  --superposition_flag                    true
% 2.17/0.92  --sup_passive_queue_type                priority_queues
% 2.17/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.92  --demod_completeness_check              fast
% 2.17/0.92  --demod_use_ground                      true
% 2.17/0.92  --sup_to_prop_solver                    passive
% 2.17/0.92  --sup_prop_simpl_new                    true
% 2.17/0.92  --sup_prop_simpl_given                  true
% 2.17/0.92  --sup_fun_splitting                     false
% 2.17/0.92  --sup_smt_interval                      50000
% 2.17/0.92  
% 2.17/0.92  ------ Superposition Simplification Setup
% 2.17/0.92  
% 2.17/0.92  --sup_indices_passive                   []
% 2.17/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.92  --sup_full_bw                           [BwDemod]
% 2.17/0.92  --sup_immed_triv                        [TrivRules]
% 2.17/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.92  --sup_immed_bw_main                     []
% 2.17/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.92  
% 2.17/0.92  ------ Combination Options
% 2.17/0.92  
% 2.17/0.92  --comb_res_mult                         3
% 2.17/0.92  --comb_sup_mult                         2
% 2.17/0.92  --comb_inst_mult                        10
% 2.17/0.92  
% 2.17/0.92  ------ Debug Options
% 2.17/0.92  
% 2.17/0.92  --dbg_backtrace                         false
% 2.17/0.92  --dbg_dump_prop_clauses                 false
% 2.17/0.92  --dbg_dump_prop_clauses_file            -
% 2.17/0.92  --dbg_out_stat                          false
% 2.17/0.92  
% 2.17/0.92  
% 2.17/0.92  
% 2.17/0.92  
% 2.17/0.92  ------ Proving...
% 2.17/0.92  
% 2.17/0.92  
% 2.17/0.92  % SZS status Theorem for theBenchmark.p
% 2.17/0.92  
% 2.17/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/0.92  
% 2.17/0.92  fof(f14,conjecture,(
% 2.17/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f15,negated_conjecture,(
% 2.17/0.92    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 2.17/0.92    inference(negated_conjecture,[],[f14])).
% 2.17/0.92  
% 2.17/0.92  fof(f28,plain,(
% 2.17/0.92    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.17/0.92    inference(ennf_transformation,[],[f15])).
% 2.17/0.92  
% 2.17/0.92  fof(f29,plain,(
% 2.17/0.92    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.17/0.92    inference(flattening,[],[f28])).
% 2.17/0.92  
% 2.17/0.92  fof(f30,plain,(
% 2.17/0.92    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.17/0.92    inference(nnf_transformation,[],[f29])).
% 2.17/0.92  
% 2.17/0.92  fof(f31,plain,(
% 2.17/0.92    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.17/0.92    inference(flattening,[],[f30])).
% 2.17/0.92  
% 2.17/0.92  fof(f33,plain,(
% 2.17/0.92    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.17/0.92    introduced(choice_axiom,[])).
% 2.17/0.92  
% 2.17/0.92  fof(f32,plain,(
% 2.17/0.92    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.17/0.92    introduced(choice_axiom,[])).
% 2.17/0.92  
% 2.17/0.92  fof(f34,plain,(
% 2.17/0.92    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.17/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 2.17/0.92  
% 2.17/0.92  fof(f52,plain,(
% 2.17/0.92    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 2.17/0.92    inference(cnf_transformation,[],[f34])).
% 2.17/0.92  
% 2.17/0.92  fof(f9,axiom,(
% 2.17/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f20,plain,(
% 2.17/0.92    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.92    inference(ennf_transformation,[],[f9])).
% 2.17/0.92  
% 2.17/0.92  fof(f21,plain,(
% 2.17/0.92    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.92    inference(flattening,[],[f20])).
% 2.17/0.92  
% 2.17/0.92  fof(f43,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f21])).
% 2.17/0.92  
% 2.17/0.92  fof(f50,plain,(
% 2.17/0.92    l1_pre_topc(sK0)),
% 2.17/0.92    inference(cnf_transformation,[],[f34])).
% 2.17/0.92  
% 2.17/0.92  fof(f51,plain,(
% 2.17/0.92    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.17/0.92    inference(cnf_transformation,[],[f34])).
% 2.17/0.92  
% 2.17/0.92  fof(f8,axiom,(
% 2.17/0.92    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f19,plain,(
% 2.17/0.92    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.17/0.92    inference(ennf_transformation,[],[f8])).
% 2.17/0.92  
% 2.17/0.92  fof(f42,plain,(
% 2.17/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.17/0.92    inference(cnf_transformation,[],[f19])).
% 2.17/0.92  
% 2.17/0.92  fof(f4,axiom,(
% 2.17/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f38,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f4])).
% 2.17/0.92  
% 2.17/0.92  fof(f5,axiom,(
% 2.17/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f39,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f5])).
% 2.17/0.92  
% 2.17/0.92  fof(f57,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.17/0.92    inference(definition_unfolding,[],[f38,f39,f39])).
% 2.17/0.92  
% 2.17/0.92  fof(f1,axiom,(
% 2.17/0.92    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f35,plain,(
% 2.17/0.92    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f1])).
% 2.17/0.92  
% 2.17/0.92  fof(f3,axiom,(
% 2.17/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f16,plain,(
% 2.17/0.92    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 2.17/0.92    inference(ennf_transformation,[],[f3])).
% 2.17/0.92  
% 2.17/0.92  fof(f37,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f16])).
% 2.17/0.92  
% 2.17/0.92  fof(f6,axiom,(
% 2.17/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f40,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.17/0.92    inference(cnf_transformation,[],[f6])).
% 2.17/0.92  
% 2.17/0.92  fof(f54,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.17/0.92    inference(definition_unfolding,[],[f40,f39])).
% 2.17/0.92  
% 2.17/0.92  fof(f56,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 2.17/0.92    inference(definition_unfolding,[],[f37,f54])).
% 2.17/0.92  
% 2.17/0.92  fof(f2,axiom,(
% 2.17/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f36,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.17/0.92    inference(cnf_transformation,[],[f2])).
% 2.17/0.92  
% 2.17/0.92  fof(f55,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 2.17/0.92    inference(definition_unfolding,[],[f36,f54,f54])).
% 2.17/0.92  
% 2.17/0.92  fof(f10,axiom,(
% 2.17/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f22,plain,(
% 2.17/0.92    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.17/0.92    inference(ennf_transformation,[],[f10])).
% 2.17/0.92  
% 2.17/0.92  fof(f23,plain,(
% 2.17/0.92    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.17/0.92    inference(flattening,[],[f22])).
% 2.17/0.92  
% 2.17/0.92  fof(f45,plain,(
% 2.17/0.92    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f23])).
% 2.17/0.92  
% 2.17/0.92  fof(f7,axiom,(
% 2.17/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f17,plain,(
% 2.17/0.92    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.17/0.92    inference(ennf_transformation,[],[f7])).
% 2.17/0.92  
% 2.17/0.92  fof(f18,plain,(
% 2.17/0.92    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.17/0.92    inference(flattening,[],[f17])).
% 2.17/0.92  
% 2.17/0.92  fof(f41,plain,(
% 2.17/0.92    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.17/0.92    inference(cnf_transformation,[],[f18])).
% 2.17/0.92  
% 2.17/0.92  fof(f58,plain,(
% 2.17/0.92    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.17/0.92    inference(definition_unfolding,[],[f41,f54])).
% 2.17/0.92  
% 2.17/0.92  fof(f13,axiom,(
% 2.17/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f27,plain,(
% 2.17/0.92    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.92    inference(ennf_transformation,[],[f13])).
% 2.17/0.92  
% 2.17/0.92  fof(f48,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f27])).
% 2.17/0.92  
% 2.17/0.92  fof(f12,axiom,(
% 2.17/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.17/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.92  
% 2.17/0.92  fof(f26,plain,(
% 2.17/0.92    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.92    inference(ennf_transformation,[],[f12])).
% 2.17/0.92  
% 2.17/0.92  fof(f47,plain,(
% 2.17/0.92    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f26])).
% 2.17/0.92  
% 2.17/0.92  fof(f53,plain,(
% 2.17/0.92    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 2.17/0.92    inference(cnf_transformation,[],[f34])).
% 2.17/0.92  
% 2.17/0.92  fof(f44,plain,(
% 2.17/0.92    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.17/0.92    inference(cnf_transformation,[],[f21])).
% 2.17/0.92  
% 2.17/0.92  fof(f49,plain,(
% 2.17/0.92    v2_pre_topc(sK0)),
% 2.17/0.92    inference(cnf_transformation,[],[f34])).
% 2.17/0.92  
% 2.17/0.92  cnf(c_13,negated_conjecture,
% 2.17/0.92      ( v4_pre_topc(sK1,sK0)
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.17/0.92      inference(cnf_transformation,[],[f52]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_120,plain,
% 2.17/0.92      ( v4_pre_topc(sK1,sK0)
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.17/0.92      inference(prop_impl,[status(thm)],[c_13]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_7,plain,
% 2.17/0.92      ( ~ v4_pre_topc(X0,X1)
% 2.17/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | ~ l1_pre_topc(X1)
% 2.17/0.92      | k2_pre_topc(X1,X0) = X0 ),
% 2.17/0.92      inference(cnf_transformation,[],[f43]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_15,negated_conjecture,
% 2.17/0.92      ( l1_pre_topc(sK0) ),
% 2.17/0.92      inference(cnf_transformation,[],[f50]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_304,plain,
% 2.17/0.92      ( ~ v4_pre_topc(X0,X1)
% 2.17/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | k2_pre_topc(X1,X0) = X0
% 2.17/0.92      | sK0 != X1 ),
% 2.17/0.92      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_305,plain,
% 2.17/0.92      ( ~ v4_pre_topc(X0,sK0)
% 2.17/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | k2_pre_topc(sK0,X0) = X0 ),
% 2.17/0.92      inference(unflattening,[status(thm)],[c_304]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_351,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 2.17/0.92      | k2_pre_topc(sK0,X0) = X0
% 2.17/0.92      | sK1 != X0
% 2.17/0.92      | sK0 != sK0 ),
% 2.17/0.92      inference(resolution_lifted,[status(thm)],[c_120,c_305]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_352,plain,
% 2.17/0.92      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 2.17/0.92      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.17/0.92      inference(unflattening,[status(thm)],[c_351]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_14,negated_conjecture,
% 2.17/0.92      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.17/0.92      inference(cnf_transformation,[],[f51]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_354,plain,
% 2.17/0.92      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 2.17/0.92      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.17/0.92      inference(global_propositional_subsumption,
% 2.17/0.92                [status(thm)],
% 2.17/0.92                [c_352,c_14]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_441,plain,
% 2.17/0.92      ( k2_pre_topc(sK0,sK1) = sK1
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.17/0.92      inference(prop_impl,[status(thm)],[c_354]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_442,plain,
% 2.17/0.92      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 2.17/0.92      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.17/0.92      inference(renaming,[status(thm)],[c_441]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_821,plain,
% 2.17/0.92      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.17/0.92      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_5,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.92      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.17/0.92      inference(cnf_transformation,[],[f42]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_822,plain,
% 2.17/0.92      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.17/0.92      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.17/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_1786,plain,
% 2.17/0.92      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_821,c_822]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_1854,plain,
% 2.17/0.92      ( k2_pre_topc(sK0,sK1) = sK1
% 2.17/0.92      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_442,c_1786]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_3,plain,
% 2.17/0.92      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 2.17/0.92      inference(cnf_transformation,[],[f57]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_0,plain,
% 2.17/0.92      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.17/0.92      inference(cnf_transformation,[],[f35]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_825,plain,
% 2.17/0.92      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.17/0.92      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_2,plain,
% 2.17/0.92      ( ~ r1_tarski(X0,X1)
% 2.17/0.92      | k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = X1 ),
% 2.17/0.92      inference(cnf_transformation,[],[f56]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_824,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = X1
% 2.17/0.92      | r1_tarski(X0,X1) != iProver_top ),
% 2.17/0.92      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_1,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 2.17/0.92      inference(cnf_transformation,[],[f55]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_842,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
% 2.17/0.92      | r1_tarski(X0,X1) != iProver_top ),
% 2.17/0.92      inference(demodulation,[status(thm)],[c_824,c_1]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_1290,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = X0 ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_825,c_842]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_2514,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,X1))) = X0 ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_3,c_1290]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_3594,plain,
% 2.17/0.92      ( k2_pre_topc(sK0,sK1) = sK1
% 2.17/0.92      | k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_1854,c_2514]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_8,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | ~ l1_pre_topc(X1) ),
% 2.17/0.92      inference(cnf_transformation,[],[f45]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_292,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | sK0 != X1 ),
% 2.17/0.92      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_293,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.17/0.92      inference(unflattening,[status(thm)],[c_292]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_818,plain,
% 2.17/0.92      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.17/0.92      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.17/0.92      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_4,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.17/0.92      | k3_tarski(k2_enumset1(X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 2.17/0.92      inference(cnf_transformation,[],[f58]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_823,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 2.17/0.92      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 2.17/0.92      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.17/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_1803,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(X0,X0,X0,k2_tops_1(sK0,X1))) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1))
% 2.17/0.92      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.17/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_818,c_823]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_3049,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
% 2.17/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_821,c_1803]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_3187,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_821,c_3049]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_11,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | ~ l1_pre_topc(X1)
% 2.17/0.92      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 2.17/0.92      inference(cnf_transformation,[],[f48]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_268,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 2.17/0.92      | sK0 != X1 ),
% 2.17/0.92      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_269,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 2.17/0.92      inference(unflattening,[status(thm)],[c_268]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_820,plain,
% 2.17/0.92      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 2.17/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.17/0.92      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_938,plain,
% 2.17/0.92      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_821,c_820]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_1802,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(X0,X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),X0,sK1)
% 2.17/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_821,c_823]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_1860,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
% 2.17/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_818,c_1802]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_2731,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_821,c_1860]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_2743,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_3,c_2731]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_3194,plain,
% 2.17/0.92      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 2.17/0.92      inference(light_normalisation,[status(thm)],[c_3187,c_938,c_2743]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_3615,plain,
% 2.17/0.92      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 2.17/0.92      inference(demodulation,[status(thm)],[c_3594,c_3194]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_10,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | ~ l1_pre_topc(X1)
% 2.17/0.92      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.17/0.92      inference(cnf_transformation,[],[f47]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_280,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.17/0.92      | sK0 != X1 ),
% 2.17/0.92      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_281,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.17/0.92      inference(unflattening,[status(thm)],[c_280]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_819,plain,
% 2.17/0.92      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.17/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.17/0.92      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_996,plain,
% 2.17/0.92      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.17/0.92      inference(superposition,[status(thm)],[c_821,c_819]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_3729,plain,
% 2.17/0.92      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.17/0.92      inference(demodulation,[status(thm)],[c_3615,c_996]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_12,negated_conjecture,
% 2.17/0.92      ( ~ v4_pre_topc(sK1,sK0)
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 2.17/0.92      inference(cnf_transformation,[],[f53]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_118,plain,
% 2.17/0.92      ( ~ v4_pre_topc(sK1,sK0)
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 2.17/0.92      inference(prop_impl,[status(thm)],[c_12]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_6,plain,
% 2.17/0.92      ( v4_pre_topc(X0,X1)
% 2.17/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | ~ l1_pre_topc(X1)
% 2.17/0.92      | ~ v2_pre_topc(X1)
% 2.17/0.92      | k2_pre_topc(X1,X0) != X0 ),
% 2.17/0.92      inference(cnf_transformation,[],[f44]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_16,negated_conjecture,
% 2.17/0.92      ( v2_pre_topc(sK0) ),
% 2.17/0.92      inference(cnf_transformation,[],[f49]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_240,plain,
% 2.17/0.92      ( v4_pre_topc(X0,X1)
% 2.17/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.92      | ~ l1_pre_topc(X1)
% 2.17/0.92      | k2_pre_topc(X1,X0) != X0
% 2.17/0.92      | sK0 != X1 ),
% 2.17/0.92      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_241,plain,
% 2.17/0.92      ( v4_pre_topc(X0,sK0)
% 2.17/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | ~ l1_pre_topc(sK0)
% 2.17/0.92      | k2_pre_topc(sK0,X0) != X0 ),
% 2.17/0.92      inference(unflattening,[status(thm)],[c_240]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_245,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | v4_pre_topc(X0,sK0)
% 2.17/0.92      | k2_pre_topc(sK0,X0) != X0 ),
% 2.17/0.92      inference(global_propositional_subsumption,
% 2.17/0.92                [status(thm)],
% 2.17/0.92                [c_241,c_15]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_246,plain,
% 2.17/0.92      ( v4_pre_topc(X0,sK0)
% 2.17/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | k2_pre_topc(sK0,X0) != X0 ),
% 2.17/0.92      inference(renaming,[status(thm)],[c_245]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_362,plain,
% 2.17/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 2.17/0.92      | k2_pre_topc(sK0,X0) != X0
% 2.17/0.92      | sK1 != X0
% 2.17/0.92      | sK0 != sK0 ),
% 2.17/0.92      inference(resolution_lifted,[status(thm)],[c_118,c_246]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_363,plain,
% 2.17/0.92      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.92      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 2.17/0.92      | k2_pre_topc(sK0,sK1) != sK1 ),
% 2.17/0.92      inference(unflattening,[status(thm)],[c_362]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(c_365,plain,
% 2.17/0.92      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 2.17/0.92      | k2_pre_topc(sK0,sK1) != sK1 ),
% 2.17/0.92      inference(global_propositional_subsumption,
% 2.17/0.92                [status(thm)],
% 2.17/0.92                [c_363,c_14]) ).
% 2.17/0.92  
% 2.17/0.92  cnf(contradiction,plain,
% 2.17/0.92      ( $false ),
% 2.17/0.92      inference(minisat,[status(thm)],[c_3729,c_3615,c_365]) ).
% 2.17/0.92  
% 2.17/0.92  
% 2.17/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/0.92  
% 2.17/0.92  ------                               Statistics
% 2.17/0.92  
% 2.17/0.92  ------ General
% 2.17/0.92  
% 2.17/0.92  abstr_ref_over_cycles:                  0
% 2.17/0.92  abstr_ref_under_cycles:                 0
% 2.17/0.92  gc_basic_clause_elim:                   0
% 2.17/0.92  forced_gc_time:                         0
% 2.17/0.92  parsing_time:                           0.008
% 2.17/0.92  unif_index_cands_time:                  0.
% 2.17/0.92  unif_index_add_time:                    0.
% 2.17/0.92  orderings_time:                         0.
% 2.17/0.92  out_proof_time:                         0.008
% 2.17/0.92  total_time:                             0.175
% 2.17/0.92  num_of_symbols:                         48
% 2.17/0.92  num_of_terms:                           4580
% 2.17/0.92  
% 2.17/0.92  ------ Preprocessing
% 2.17/0.92  
% 2.17/0.92  num_of_splits:                          0
% 2.17/0.92  num_of_split_atoms:                     0
% 2.17/0.92  num_of_reused_defs:                     0
% 2.17/0.92  num_eq_ax_congr_red:                    23
% 2.17/0.92  num_of_sem_filtered_clauses:            1
% 2.17/0.92  num_of_subtypes:                        0
% 2.17/0.92  monotx_restored_types:                  0
% 2.17/0.92  sat_num_of_epr_types:                   0
% 2.17/0.92  sat_num_of_non_cyclic_types:            0
% 2.17/0.92  sat_guarded_non_collapsed_types:        0
% 2.17/0.92  num_pure_diseq_elim:                    0
% 2.17/0.92  simp_replaced_by:                       0
% 2.17/0.92  res_preprocessed:                       86
% 2.17/0.92  prep_upred:                             0
% 2.17/0.92  prep_unflattend:                        13
% 2.17/0.92  smt_new_axioms:                         0
% 2.17/0.92  pred_elim_cands:                        2
% 2.17/0.92  pred_elim:                              3
% 2.17/0.92  pred_elim_cl:                           3
% 2.17/0.92  pred_elim_cycles:                       6
% 2.17/0.92  merged_defs:                            8
% 2.17/0.92  merged_defs_ncl:                        0
% 2.17/0.92  bin_hyper_res:                          9
% 2.17/0.92  prep_cycles:                            4
% 2.17/0.92  pred_elim_time:                         0.005
% 2.17/0.92  splitting_time:                         0.
% 2.17/0.92  sem_filter_time:                        0.
% 2.17/0.92  monotx_time:                            0.001
% 2.17/0.92  subtype_inf_time:                       0.
% 2.17/0.92  
% 2.17/0.92  ------ Problem properties
% 2.17/0.92  
% 2.17/0.92  clauses:                                14
% 2.17/0.92  conjectures:                            1
% 2.17/0.92  epr:                                    0
% 2.17/0.92  horn:                                   13
% 2.17/0.92  ground:                                 3
% 2.17/0.92  unary:                                  4
% 2.17/0.92  binary:                                 7
% 2.17/0.92  lits:                                   27
% 2.17/0.92  lits_eq:                                14
% 2.17/0.92  fd_pure:                                0
% 2.17/0.92  fd_pseudo:                              0
% 2.17/0.92  fd_cond:                                0
% 2.17/0.92  fd_pseudo_cond:                         0
% 2.17/0.92  ac_symbols:                             0
% 2.17/0.92  
% 2.17/0.92  ------ Propositional Solver
% 2.17/0.92  
% 2.17/0.92  prop_solver_calls:                      29
% 2.17/0.92  prop_fast_solver_calls:                 502
% 2.17/0.92  smt_solver_calls:                       0
% 2.17/0.92  smt_fast_solver_calls:                  0
% 2.17/0.92  prop_num_of_clauses:                    1683
% 2.17/0.92  prop_preprocess_simplified:             4763
% 2.17/0.92  prop_fo_subsumed:                       4
% 2.17/0.92  prop_solver_time:                       0.
% 2.17/0.92  smt_solver_time:                        0.
% 2.17/0.92  smt_fast_solver_time:                   0.
% 2.17/0.92  prop_fast_solver_time:                  0.
% 2.17/0.92  prop_unsat_core_time:                   0.
% 2.17/0.92  
% 2.17/0.92  ------ QBF
% 2.17/0.92  
% 2.17/0.92  qbf_q_res:                              0
% 2.17/0.92  qbf_num_tautologies:                    0
% 2.17/0.92  qbf_prep_cycles:                        0
% 2.17/0.92  
% 2.17/0.92  ------ BMC1
% 2.17/0.92  
% 2.17/0.92  bmc1_current_bound:                     -1
% 2.17/0.92  bmc1_last_solved_bound:                 -1
% 2.17/0.92  bmc1_unsat_core_size:                   -1
% 2.17/0.92  bmc1_unsat_core_parents_size:           -1
% 2.17/0.92  bmc1_merge_next_fun:                    0
% 2.17/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.92  
% 2.17/0.92  ------ Instantiation
% 2.17/0.92  
% 2.17/0.92  inst_num_of_clauses:                    527
% 2.17/0.92  inst_num_in_passive:                    243
% 2.17/0.92  inst_num_in_active:                     243
% 2.17/0.92  inst_num_in_unprocessed:                41
% 2.17/0.92  inst_num_of_loops:                      260
% 2.17/0.92  inst_num_of_learning_restarts:          0
% 2.17/0.92  inst_num_moves_active_passive:          14
% 2.17/0.92  inst_lit_activity:                      0
% 2.17/0.92  inst_lit_activity_moves:                0
% 2.17/0.92  inst_num_tautologies:                   0
% 2.17/0.92  inst_num_prop_implied:                  0
% 2.17/0.92  inst_num_existing_simplified:           0
% 2.17/0.92  inst_num_eq_res_simplified:             0
% 2.17/0.92  inst_num_child_elim:                    0
% 2.17/0.92  inst_num_of_dismatching_blockings:      50
% 2.17/0.92  inst_num_of_non_proper_insts:           341
% 2.17/0.92  inst_num_of_duplicates:                 0
% 2.17/0.92  inst_inst_num_from_inst_to_res:         0
% 2.17/0.92  inst_dismatching_checking_time:         0.
% 2.17/0.92  
% 2.17/0.92  ------ Resolution
% 2.17/0.92  
% 2.17/0.92  res_num_of_clauses:                     0
% 2.17/0.92  res_num_in_passive:                     0
% 2.17/0.92  res_num_in_active:                      0
% 2.17/0.92  res_num_of_loops:                       90
% 2.17/0.92  res_forward_subset_subsumed:            19
% 2.17/0.92  res_backward_subset_subsumed:           0
% 2.17/0.92  res_forward_subsumed:                   0
% 2.17/0.92  res_backward_subsumed:                  0
% 2.17/0.92  res_forward_subsumption_resolution:     0
% 2.17/0.92  res_backward_subsumption_resolution:    0
% 2.17/0.92  res_clause_to_clause_subsumption:       168
% 2.17/0.92  res_orphan_elimination:                 0
% 2.17/0.92  res_tautology_del:                      51
% 2.17/0.92  res_num_eq_res_simplified:              1
% 2.17/0.92  res_num_sel_changes:                    0
% 2.17/0.92  res_moves_from_active_to_pass:          0
% 2.17/0.92  
% 2.17/0.92  ------ Superposition
% 2.17/0.92  
% 2.17/0.92  sup_time_total:                         0.
% 2.17/0.92  sup_time_generating:                    0.
% 2.17/0.92  sup_time_sim_full:                      0.
% 2.17/0.92  sup_time_sim_immed:                     0.
% 2.17/0.92  
% 2.17/0.92  sup_num_of_clauses:                     50
% 2.17/0.92  sup_num_in_active:                      38
% 2.17/0.92  sup_num_in_passive:                     12
% 2.17/0.92  sup_num_of_loops:                       50
% 2.17/0.92  sup_fw_superposition:                   41
% 2.17/0.92  sup_bw_superposition:                   10
% 2.17/0.92  sup_immediate_simplified:               6
% 2.17/0.92  sup_given_eliminated:                   0
% 2.17/0.92  comparisons_done:                       0
% 2.17/0.92  comparisons_avoided:                    6
% 2.17/0.92  
% 2.17/0.92  ------ Simplifications
% 2.17/0.92  
% 2.17/0.92  
% 2.17/0.92  sim_fw_subset_subsumed:                 0
% 2.17/0.92  sim_bw_subset_subsumed:                 6
% 2.17/0.92  sim_fw_subsumed:                        0
% 2.17/0.92  sim_bw_subsumed:                        0
% 2.17/0.92  sim_fw_subsumption_res:                 0
% 2.17/0.92  sim_bw_subsumption_res:                 0
% 2.17/0.92  sim_tautology_del:                      1
% 2.17/0.92  sim_eq_tautology_del:                   1
% 2.17/0.92  sim_eq_res_simp:                        1
% 2.17/0.92  sim_fw_demodulated:                     2
% 2.17/0.92  sim_bw_demodulated:                     10
% 2.17/0.92  sim_light_normalised:                   1
% 2.17/0.92  sim_joinable_taut:                      0
% 2.17/0.92  sim_joinable_simp:                      0
% 2.17/0.92  sim_ac_normalised:                      0
% 2.17/0.92  sim_smt_subsumption:                    0
% 2.17/0.92  
%------------------------------------------------------------------------------

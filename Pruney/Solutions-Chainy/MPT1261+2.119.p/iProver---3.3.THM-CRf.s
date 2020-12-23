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
% DateTime   : Thu Dec  3 12:14:41 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 714 expanded)
%              Number of clauses        :   65 ( 175 expanded)
%              Number of leaves         :   22 ( 174 expanded)
%              Depth                    :   20
%              Number of atoms          :  326 (2347 expanded)
%              Number of equality atoms :  158 ( 908 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f40])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f17,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_858,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_863,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_858,c_2])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_855,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2501,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_863,c_855])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_854,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2499,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_854,c_855])).

cnf(c_9237,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_2501,c_2499])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_138,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_336,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_337,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_138,c_337])).

cnf(c_384,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_386,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_16])).

cnf(c_477,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_386])).

cnf(c_478,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_477])).

cnf(c_9341,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_9237,c_478])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_857,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_856,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2225,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_856])).

cnf(c_2518,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),X0,X1)) = k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),X0,X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_2225])).

cnf(c_4929,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(superposition,[status(thm)],[c_854,c_2518])).

cnf(c_9304,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X0)) = k2_xboole_0(sK1,k7_subset_1(sK1,sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_9237,c_4929])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_xboole_0(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_1])).

cnf(c_853,plain,
    ( k2_xboole_0(X0,X1) = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_3280,plain,
    ( k2_xboole_0(k7_subset_1(X0,X1,X2),X0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_853])).

cnf(c_5942,plain,
    ( k2_xboole_0(k7_subset_1(X0,X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_863,c_3280])).

cnf(c_6937,plain,
    ( k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_5942])).

cnf(c_9306,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_9304,c_6937])).

cnf(c_9671,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_9341,c_9306])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_852,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_1029,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_854,c_852])).

cnf(c_9690,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_9671,c_1029])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_851,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_1064,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_854,c_851])).

cnf(c_9723,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_9690,c_1064])).

cnf(c_14,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_136,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_272,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_273,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_17])).

cnf(c_278,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_136,c_278])).

cnf(c_395,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_397,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9723,c_9690,c_397])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.67/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.67/1.02  
% 0.67/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.67/1.02  
% 0.67/1.02  ------  iProver source info
% 0.67/1.02  
% 0.67/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.67/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.67/1.02  git: non_committed_changes: false
% 0.67/1.02  git: last_make_outside_of_git: false
% 0.67/1.02  
% 0.67/1.02  ------ 
% 0.67/1.02  
% 0.67/1.02  ------ Input Options
% 0.67/1.02  
% 0.67/1.02  --out_options                           all
% 0.67/1.02  --tptp_safe_out                         true
% 0.67/1.02  --problem_path                          ""
% 0.67/1.02  --include_path                          ""
% 0.67/1.02  --clausifier                            res/vclausify_rel
% 0.67/1.02  --clausifier_options                    --mode clausify
% 0.67/1.02  --stdin                                 false
% 0.67/1.02  --stats_out                             all
% 0.67/1.02  
% 0.67/1.02  ------ General Options
% 0.67/1.02  
% 0.67/1.02  --fof                                   false
% 0.67/1.02  --time_out_real                         305.
% 0.67/1.02  --time_out_virtual                      -1.
% 0.67/1.02  --symbol_type_check                     false
% 0.67/1.02  --clausify_out                          false
% 0.67/1.02  --sig_cnt_out                           false
% 0.67/1.03  --trig_cnt_out                          false
% 0.67/1.03  --trig_cnt_out_tolerance                1.
% 0.67/1.03  --trig_cnt_out_sk_spl                   false
% 0.67/1.03  --abstr_cl_out                          false
% 0.67/1.03  
% 0.67/1.03  ------ Global Options
% 0.67/1.03  
% 0.67/1.03  --schedule                              default
% 0.67/1.03  --add_important_lit                     false
% 0.67/1.03  --prop_solver_per_cl                    1000
% 0.67/1.03  --min_unsat_core                        false
% 0.67/1.03  --soft_assumptions                      false
% 0.67/1.03  --soft_lemma_size                       3
% 0.67/1.03  --prop_impl_unit_size                   0
% 0.67/1.03  --prop_impl_unit                        []
% 0.67/1.03  --share_sel_clauses                     true
% 0.67/1.03  --reset_solvers                         false
% 0.67/1.03  --bc_imp_inh                            [conj_cone]
% 0.67/1.03  --conj_cone_tolerance                   3.
% 0.67/1.03  --extra_neg_conj                        none
% 0.67/1.03  --large_theory_mode                     true
% 0.67/1.03  --prolific_symb_bound                   200
% 0.67/1.03  --lt_threshold                          2000
% 0.67/1.03  --clause_weak_htbl                      true
% 0.67/1.03  --gc_record_bc_elim                     false
% 0.67/1.03  
% 0.67/1.03  ------ Preprocessing Options
% 0.67/1.03  
% 0.67/1.03  --preprocessing_flag                    true
% 0.67/1.03  --time_out_prep_mult                    0.1
% 0.67/1.03  --splitting_mode                        input
% 0.67/1.03  --splitting_grd                         true
% 0.67/1.03  --splitting_cvd                         false
% 0.67/1.03  --splitting_cvd_svl                     false
% 0.67/1.03  --splitting_nvd                         32
% 0.67/1.03  --sub_typing                            true
% 0.67/1.03  --prep_gs_sim                           true
% 0.67/1.03  --prep_unflatten                        true
% 0.67/1.03  --prep_res_sim                          true
% 0.67/1.03  --prep_upred                            true
% 0.67/1.03  --prep_sem_filter                       exhaustive
% 0.67/1.03  --prep_sem_filter_out                   false
% 0.67/1.03  --pred_elim                             true
% 0.67/1.03  --res_sim_input                         true
% 0.67/1.03  --eq_ax_congr_red                       true
% 0.67/1.03  --pure_diseq_elim                       true
% 0.67/1.03  --brand_transform                       false
% 0.67/1.03  --non_eq_to_eq                          false
% 0.67/1.03  --prep_def_merge                        true
% 0.67/1.03  --prep_def_merge_prop_impl              false
% 0.67/1.03  --prep_def_merge_mbd                    true
% 0.67/1.03  --prep_def_merge_tr_red                 false
% 0.67/1.03  --prep_def_merge_tr_cl                  false
% 0.67/1.03  --smt_preprocessing                     true
% 0.67/1.03  --smt_ac_axioms                         fast
% 0.67/1.03  --preprocessed_out                      false
% 0.67/1.03  --preprocessed_stats                    false
% 0.67/1.03  
% 0.67/1.03  ------ Abstraction refinement Options
% 0.67/1.03  
% 0.67/1.03  --abstr_ref                             []
% 0.67/1.03  --abstr_ref_prep                        false
% 0.67/1.03  --abstr_ref_until_sat                   false
% 0.67/1.03  --abstr_ref_sig_restrict                funpre
% 0.67/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.67/1.03  --abstr_ref_under                       []
% 0.67/1.03  
% 0.67/1.03  ------ SAT Options
% 0.67/1.03  
% 0.67/1.03  --sat_mode                              false
% 0.67/1.03  --sat_fm_restart_options                ""
% 0.67/1.03  --sat_gr_def                            false
% 0.67/1.03  --sat_epr_types                         true
% 0.67/1.03  --sat_non_cyclic_types                  false
% 0.67/1.03  --sat_finite_models                     false
% 0.67/1.03  --sat_fm_lemmas                         false
% 0.67/1.03  --sat_fm_prep                           false
% 0.67/1.03  --sat_fm_uc_incr                        true
% 0.67/1.03  --sat_out_model                         small
% 0.67/1.03  --sat_out_clauses                       false
% 0.67/1.03  
% 0.67/1.03  ------ QBF Options
% 0.67/1.03  
% 0.67/1.03  --qbf_mode                              false
% 0.67/1.03  --qbf_elim_univ                         false
% 0.67/1.03  --qbf_dom_inst                          none
% 0.67/1.03  --qbf_dom_pre_inst                      false
% 0.67/1.03  --qbf_sk_in                             false
% 0.67/1.03  --qbf_pred_elim                         true
% 0.67/1.03  --qbf_split                             512
% 0.67/1.03  
% 0.67/1.03  ------ BMC1 Options
% 0.67/1.03  
% 0.67/1.03  --bmc1_incremental                      false
% 0.67/1.03  --bmc1_axioms                           reachable_all
% 0.67/1.03  --bmc1_min_bound                        0
% 0.67/1.03  --bmc1_max_bound                        -1
% 0.67/1.03  --bmc1_max_bound_default                -1
% 0.67/1.03  --bmc1_symbol_reachability              true
% 0.67/1.03  --bmc1_property_lemmas                  false
% 0.67/1.03  --bmc1_k_induction                      false
% 0.67/1.03  --bmc1_non_equiv_states                 false
% 0.67/1.03  --bmc1_deadlock                         false
% 0.67/1.03  --bmc1_ucm                              false
% 0.67/1.03  --bmc1_add_unsat_core                   none
% 0.67/1.03  --bmc1_unsat_core_children              false
% 0.67/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.67/1.03  --bmc1_out_stat                         full
% 0.67/1.03  --bmc1_ground_init                      false
% 0.67/1.03  --bmc1_pre_inst_next_state              false
% 0.67/1.03  --bmc1_pre_inst_state                   false
% 0.67/1.03  --bmc1_pre_inst_reach_state             false
% 0.67/1.03  --bmc1_out_unsat_core                   false
% 0.67/1.03  --bmc1_aig_witness_out                  false
% 0.67/1.03  --bmc1_verbose                          false
% 0.67/1.03  --bmc1_dump_clauses_tptp                false
% 0.67/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.67/1.03  --bmc1_dump_file                        -
% 0.67/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.67/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.67/1.03  --bmc1_ucm_extend_mode                  1
% 0.67/1.03  --bmc1_ucm_init_mode                    2
% 0.67/1.03  --bmc1_ucm_cone_mode                    none
% 0.67/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.67/1.03  --bmc1_ucm_relax_model                  4
% 0.67/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.67/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.67/1.03  --bmc1_ucm_layered_model                none
% 0.67/1.03  --bmc1_ucm_max_lemma_size               10
% 0.67/1.03  
% 0.67/1.03  ------ AIG Options
% 0.67/1.03  
% 0.67/1.03  --aig_mode                              false
% 0.67/1.03  
% 0.67/1.03  ------ Instantiation Options
% 0.67/1.03  
% 0.67/1.03  --instantiation_flag                    true
% 0.67/1.03  --inst_sos_flag                         false
% 0.67/1.03  --inst_sos_phase                        true
% 0.67/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.67/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.67/1.03  --inst_lit_sel_side                     num_symb
% 0.67/1.03  --inst_solver_per_active                1400
% 0.67/1.03  --inst_solver_calls_frac                1.
% 0.67/1.03  --inst_passive_queue_type               priority_queues
% 0.67/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.67/1.03  --inst_passive_queues_freq              [25;2]
% 0.67/1.03  --inst_dismatching                      true
% 0.67/1.03  --inst_eager_unprocessed_to_passive     true
% 0.67/1.03  --inst_prop_sim_given                   true
% 0.67/1.03  --inst_prop_sim_new                     false
% 0.67/1.03  --inst_subs_new                         false
% 0.67/1.03  --inst_eq_res_simp                      false
% 0.67/1.03  --inst_subs_given                       false
% 0.67/1.03  --inst_orphan_elimination               true
% 0.67/1.03  --inst_learning_loop_flag               true
% 0.67/1.03  --inst_learning_start                   3000
% 0.67/1.03  --inst_learning_factor                  2
% 0.67/1.03  --inst_start_prop_sim_after_learn       3
% 0.67/1.03  --inst_sel_renew                        solver
% 0.67/1.03  --inst_lit_activity_flag                true
% 0.67/1.03  --inst_restr_to_given                   false
% 0.67/1.03  --inst_activity_threshold               500
% 0.67/1.03  --inst_out_proof                        true
% 0.67/1.03  
% 0.67/1.03  ------ Resolution Options
% 0.67/1.03  
% 0.67/1.03  --resolution_flag                       true
% 0.67/1.03  --res_lit_sel                           adaptive
% 0.67/1.03  --res_lit_sel_side                      none
% 0.67/1.03  --res_ordering                          kbo
% 0.67/1.03  --res_to_prop_solver                    active
% 0.67/1.03  --res_prop_simpl_new                    false
% 0.67/1.03  --res_prop_simpl_given                  true
% 0.67/1.03  --res_passive_queue_type                priority_queues
% 0.67/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.67/1.03  --res_passive_queues_freq               [15;5]
% 0.67/1.03  --res_forward_subs                      full
% 0.67/1.03  --res_backward_subs                     full
% 0.67/1.03  --res_forward_subs_resolution           true
% 0.67/1.03  --res_backward_subs_resolution          true
% 0.67/1.03  --res_orphan_elimination                true
% 0.67/1.03  --res_time_limit                        2.
% 0.67/1.03  --res_out_proof                         true
% 0.67/1.03  
% 0.67/1.03  ------ Superposition Options
% 0.67/1.03  
% 0.67/1.03  --superposition_flag                    true
% 0.67/1.03  --sup_passive_queue_type                priority_queues
% 0.67/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.67/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.67/1.03  --demod_completeness_check              fast
% 0.67/1.03  --demod_use_ground                      true
% 0.67/1.03  --sup_to_prop_solver                    passive
% 0.67/1.03  --sup_prop_simpl_new                    true
% 0.67/1.03  --sup_prop_simpl_given                  true
% 0.67/1.03  --sup_fun_splitting                     false
% 0.67/1.03  --sup_smt_interval                      50000
% 0.67/1.03  
% 0.67/1.03  ------ Superposition Simplification Setup
% 0.67/1.03  
% 0.67/1.03  --sup_indices_passive                   []
% 0.67/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.67/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.03  --sup_full_bw                           [BwDemod]
% 0.67/1.03  --sup_immed_triv                        [TrivRules]
% 0.67/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.67/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.03  --sup_immed_bw_main                     []
% 0.67/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.67/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.03  
% 0.67/1.03  ------ Combination Options
% 0.67/1.03  
% 0.67/1.03  --comb_res_mult                         3
% 0.67/1.03  --comb_sup_mult                         2
% 0.67/1.03  --comb_inst_mult                        10
% 0.67/1.03  
% 0.67/1.03  ------ Debug Options
% 0.67/1.03  
% 0.67/1.03  --dbg_backtrace                         false
% 0.67/1.03  --dbg_dump_prop_clauses                 false
% 0.67/1.03  --dbg_dump_prop_clauses_file            -
% 0.67/1.03  --dbg_out_stat                          false
% 0.67/1.03  ------ Parsing...
% 0.67/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.67/1.03  
% 0.67/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.67/1.03  
% 0.67/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.67/1.03  
% 0.67/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.67/1.03  ------ Proving...
% 0.67/1.03  ------ Problem Properties 
% 0.67/1.03  
% 0.67/1.03  
% 0.67/1.03  clauses                                 15
% 0.67/1.03  conjectures                             1
% 0.67/1.03  EPR                                     0
% 0.67/1.03  Horn                                    14
% 0.67/1.03  unary                                   4
% 0.67/1.03  binary                                  8
% 0.67/1.03  lits                                    29
% 0.67/1.03  lits eq                                 14
% 0.67/1.03  fd_pure                                 0
% 0.67/1.03  fd_pseudo                               0
% 0.67/1.03  fd_cond                                 0
% 0.67/1.03  fd_pseudo_cond                          0
% 0.67/1.03  AC symbols                              0
% 0.67/1.03  
% 0.67/1.03  ------ Schedule dynamic 5 is on 
% 0.67/1.03  
% 0.67/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.67/1.03  
% 0.67/1.03  
% 0.67/1.03  ------ 
% 0.67/1.03  Current options:
% 0.67/1.03  ------ 
% 0.67/1.03  
% 0.67/1.03  ------ Input Options
% 0.67/1.03  
% 0.67/1.03  --out_options                           all
% 0.67/1.03  --tptp_safe_out                         true
% 0.67/1.03  --problem_path                          ""
% 0.67/1.03  --include_path                          ""
% 0.67/1.03  --clausifier                            res/vclausify_rel
% 0.67/1.03  --clausifier_options                    --mode clausify
% 0.67/1.03  --stdin                                 false
% 0.67/1.03  --stats_out                             all
% 0.67/1.03  
% 0.67/1.03  ------ General Options
% 0.67/1.03  
% 0.67/1.03  --fof                                   false
% 0.67/1.03  --time_out_real                         305.
% 0.67/1.03  --time_out_virtual                      -1.
% 0.67/1.03  --symbol_type_check                     false
% 0.67/1.03  --clausify_out                          false
% 0.67/1.03  --sig_cnt_out                           false
% 0.67/1.03  --trig_cnt_out                          false
% 0.67/1.03  --trig_cnt_out_tolerance                1.
% 0.67/1.03  --trig_cnt_out_sk_spl                   false
% 0.67/1.03  --abstr_cl_out                          false
% 0.67/1.03  
% 0.67/1.03  ------ Global Options
% 0.67/1.03  
% 0.67/1.03  --schedule                              default
% 0.67/1.03  --add_important_lit                     false
% 0.67/1.03  --prop_solver_per_cl                    1000
% 0.67/1.03  --min_unsat_core                        false
% 0.67/1.03  --soft_assumptions                      false
% 0.67/1.03  --soft_lemma_size                       3
% 0.67/1.03  --prop_impl_unit_size                   0
% 0.67/1.03  --prop_impl_unit                        []
% 0.67/1.03  --share_sel_clauses                     true
% 0.67/1.03  --reset_solvers                         false
% 0.67/1.03  --bc_imp_inh                            [conj_cone]
% 0.67/1.03  --conj_cone_tolerance                   3.
% 0.67/1.03  --extra_neg_conj                        none
% 0.67/1.03  --large_theory_mode                     true
% 0.67/1.03  --prolific_symb_bound                   200
% 0.67/1.03  --lt_threshold                          2000
% 0.67/1.03  --clause_weak_htbl                      true
% 0.67/1.03  --gc_record_bc_elim                     false
% 0.67/1.03  
% 0.67/1.03  ------ Preprocessing Options
% 0.67/1.03  
% 0.67/1.03  --preprocessing_flag                    true
% 0.67/1.03  --time_out_prep_mult                    0.1
% 0.67/1.03  --splitting_mode                        input
% 0.67/1.03  --splitting_grd                         true
% 0.67/1.03  --splitting_cvd                         false
% 0.67/1.03  --splitting_cvd_svl                     false
% 0.67/1.03  --splitting_nvd                         32
% 0.67/1.03  --sub_typing                            true
% 0.67/1.03  --prep_gs_sim                           true
% 0.67/1.03  --prep_unflatten                        true
% 0.67/1.03  --prep_res_sim                          true
% 0.67/1.03  --prep_upred                            true
% 0.67/1.03  --prep_sem_filter                       exhaustive
% 0.67/1.03  --prep_sem_filter_out                   false
% 0.67/1.03  --pred_elim                             true
% 0.67/1.03  --res_sim_input                         true
% 0.67/1.03  --eq_ax_congr_red                       true
% 0.67/1.03  --pure_diseq_elim                       true
% 0.67/1.03  --brand_transform                       false
% 0.67/1.03  --non_eq_to_eq                          false
% 0.67/1.03  --prep_def_merge                        true
% 0.67/1.03  --prep_def_merge_prop_impl              false
% 0.67/1.03  --prep_def_merge_mbd                    true
% 0.67/1.03  --prep_def_merge_tr_red                 false
% 0.67/1.03  --prep_def_merge_tr_cl                  false
% 0.67/1.03  --smt_preprocessing                     true
% 0.67/1.03  --smt_ac_axioms                         fast
% 0.67/1.03  --preprocessed_out                      false
% 0.67/1.03  --preprocessed_stats                    false
% 0.67/1.03  
% 0.67/1.03  ------ Abstraction refinement Options
% 0.67/1.03  
% 0.67/1.03  --abstr_ref                             []
% 0.67/1.03  --abstr_ref_prep                        false
% 0.67/1.03  --abstr_ref_until_sat                   false
% 0.67/1.03  --abstr_ref_sig_restrict                funpre
% 0.67/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.67/1.03  --abstr_ref_under                       []
% 0.67/1.03  
% 0.67/1.03  ------ SAT Options
% 0.67/1.03  
% 0.67/1.03  --sat_mode                              false
% 0.67/1.03  --sat_fm_restart_options                ""
% 0.67/1.03  --sat_gr_def                            false
% 0.67/1.03  --sat_epr_types                         true
% 0.67/1.03  --sat_non_cyclic_types                  false
% 0.67/1.03  --sat_finite_models                     false
% 0.67/1.03  --sat_fm_lemmas                         false
% 0.67/1.03  --sat_fm_prep                           false
% 0.67/1.03  --sat_fm_uc_incr                        true
% 0.67/1.03  --sat_out_model                         small
% 0.67/1.03  --sat_out_clauses                       false
% 0.67/1.03  
% 0.67/1.03  ------ QBF Options
% 0.67/1.03  
% 0.67/1.03  --qbf_mode                              false
% 0.67/1.03  --qbf_elim_univ                         false
% 0.67/1.03  --qbf_dom_inst                          none
% 0.67/1.03  --qbf_dom_pre_inst                      false
% 0.67/1.03  --qbf_sk_in                             false
% 0.67/1.03  --qbf_pred_elim                         true
% 0.67/1.03  --qbf_split                             512
% 0.67/1.03  
% 0.67/1.03  ------ BMC1 Options
% 0.67/1.03  
% 0.67/1.03  --bmc1_incremental                      false
% 0.67/1.03  --bmc1_axioms                           reachable_all
% 0.67/1.03  --bmc1_min_bound                        0
% 0.67/1.03  --bmc1_max_bound                        -1
% 0.67/1.03  --bmc1_max_bound_default                -1
% 0.67/1.03  --bmc1_symbol_reachability              true
% 0.67/1.03  --bmc1_property_lemmas                  false
% 0.67/1.03  --bmc1_k_induction                      false
% 0.67/1.03  --bmc1_non_equiv_states                 false
% 0.67/1.03  --bmc1_deadlock                         false
% 0.67/1.03  --bmc1_ucm                              false
% 0.67/1.03  --bmc1_add_unsat_core                   none
% 0.67/1.03  --bmc1_unsat_core_children              false
% 0.67/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.67/1.03  --bmc1_out_stat                         full
% 0.67/1.03  --bmc1_ground_init                      false
% 0.67/1.03  --bmc1_pre_inst_next_state              false
% 0.67/1.03  --bmc1_pre_inst_state                   false
% 0.67/1.03  --bmc1_pre_inst_reach_state             false
% 0.67/1.03  --bmc1_out_unsat_core                   false
% 0.67/1.03  --bmc1_aig_witness_out                  false
% 0.67/1.03  --bmc1_verbose                          false
% 0.67/1.03  --bmc1_dump_clauses_tptp                false
% 0.67/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.67/1.03  --bmc1_dump_file                        -
% 0.67/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.67/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.67/1.03  --bmc1_ucm_extend_mode                  1
% 0.67/1.03  --bmc1_ucm_init_mode                    2
% 0.67/1.03  --bmc1_ucm_cone_mode                    none
% 0.67/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.67/1.03  --bmc1_ucm_relax_model                  4
% 0.67/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.67/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.67/1.03  --bmc1_ucm_layered_model                none
% 0.67/1.03  --bmc1_ucm_max_lemma_size               10
% 0.67/1.03  
% 0.67/1.03  ------ AIG Options
% 0.67/1.03  
% 0.67/1.03  --aig_mode                              false
% 0.67/1.03  
% 0.67/1.03  ------ Instantiation Options
% 0.67/1.03  
% 0.67/1.03  --instantiation_flag                    true
% 0.67/1.03  --inst_sos_flag                         false
% 0.67/1.03  --inst_sos_phase                        true
% 0.67/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.67/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.67/1.03  --inst_lit_sel_side                     none
% 0.67/1.03  --inst_solver_per_active                1400
% 0.67/1.03  --inst_solver_calls_frac                1.
% 0.67/1.03  --inst_passive_queue_type               priority_queues
% 0.67/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.67/1.03  --inst_passive_queues_freq              [25;2]
% 0.67/1.03  --inst_dismatching                      true
% 0.67/1.03  --inst_eager_unprocessed_to_passive     true
% 0.67/1.03  --inst_prop_sim_given                   true
% 0.67/1.03  --inst_prop_sim_new                     false
% 0.67/1.03  --inst_subs_new                         false
% 0.67/1.03  --inst_eq_res_simp                      false
% 0.67/1.03  --inst_subs_given                       false
% 0.67/1.03  --inst_orphan_elimination               true
% 0.67/1.03  --inst_learning_loop_flag               true
% 0.67/1.03  --inst_learning_start                   3000
% 0.67/1.03  --inst_learning_factor                  2
% 0.67/1.03  --inst_start_prop_sim_after_learn       3
% 0.67/1.03  --inst_sel_renew                        solver
% 0.67/1.03  --inst_lit_activity_flag                true
% 0.67/1.03  --inst_restr_to_given                   false
% 0.67/1.03  --inst_activity_threshold               500
% 0.67/1.03  --inst_out_proof                        true
% 0.67/1.03  
% 0.67/1.03  ------ Resolution Options
% 0.67/1.03  
% 0.67/1.03  --resolution_flag                       false
% 0.67/1.03  --res_lit_sel                           adaptive
% 0.67/1.03  --res_lit_sel_side                      none
% 0.67/1.03  --res_ordering                          kbo
% 0.67/1.03  --res_to_prop_solver                    active
% 0.67/1.03  --res_prop_simpl_new                    false
% 0.67/1.03  --res_prop_simpl_given                  true
% 0.67/1.03  --res_passive_queue_type                priority_queues
% 0.67/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.67/1.03  --res_passive_queues_freq               [15;5]
% 0.67/1.03  --res_forward_subs                      full
% 0.67/1.03  --res_backward_subs                     full
% 0.67/1.03  --res_forward_subs_resolution           true
% 0.67/1.03  --res_backward_subs_resolution          true
% 0.67/1.03  --res_orphan_elimination                true
% 0.67/1.03  --res_time_limit                        2.
% 0.67/1.03  --res_out_proof                         true
% 0.67/1.03  
% 0.67/1.03  ------ Superposition Options
% 0.67/1.03  
% 0.67/1.03  --superposition_flag                    true
% 0.67/1.03  --sup_passive_queue_type                priority_queues
% 0.67/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.67/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.67/1.03  --demod_completeness_check              fast
% 0.67/1.03  --demod_use_ground                      true
% 0.67/1.03  --sup_to_prop_solver                    passive
% 0.67/1.03  --sup_prop_simpl_new                    true
% 0.67/1.03  --sup_prop_simpl_given                  true
% 0.67/1.03  --sup_fun_splitting                     false
% 0.67/1.03  --sup_smt_interval                      50000
% 0.67/1.03  
% 0.67/1.03  ------ Superposition Simplification Setup
% 0.67/1.03  
% 0.67/1.03  --sup_indices_passive                   []
% 0.67/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.67/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.03  --sup_full_bw                           [BwDemod]
% 0.67/1.03  --sup_immed_triv                        [TrivRules]
% 0.67/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.67/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.03  --sup_immed_bw_main                     []
% 0.67/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.67/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.03  
% 0.67/1.03  ------ Combination Options
% 0.67/1.03  
% 0.67/1.03  --comb_res_mult                         3
% 0.67/1.03  --comb_sup_mult                         2
% 0.67/1.03  --comb_inst_mult                        10
% 0.67/1.03  
% 0.67/1.03  ------ Debug Options
% 0.67/1.03  
% 0.67/1.03  --dbg_backtrace                         false
% 0.67/1.03  --dbg_dump_prop_clauses                 false
% 0.67/1.03  --dbg_dump_prop_clauses_file            -
% 0.67/1.03  --dbg_out_stat                          false
% 0.67/1.03  
% 0.67/1.03  
% 0.67/1.03  
% 0.67/1.03  
% 0.67/1.03  ------ Proving...
% 0.67/1.03  
% 0.67/1.03  
% 0.67/1.03  % SZS status Theorem for theBenchmark.p
% 0.67/1.03  
% 0.67/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.67/1.03  
% 0.67/1.03  fof(f11,axiom,(
% 0.67/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f56,plain,(
% 0.67/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.67/1.03    inference(cnf_transformation,[],[f11])).
% 0.67/1.03  
% 0.67/1.03  fof(f10,axiom,(
% 0.67/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f55,plain,(
% 0.67/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.67/1.03    inference(cnf_transformation,[],[f10])).
% 0.67/1.03  
% 0.67/1.03  fof(f14,axiom,(
% 0.67/1.03    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f29,plain,(
% 0.67/1.03    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.67/1.03    inference(ennf_transformation,[],[f14])).
% 0.67/1.03  
% 0.67/1.03  fof(f59,plain,(
% 0.67/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.67/1.03    inference(cnf_transformation,[],[f29])).
% 0.67/1.03  
% 0.67/1.03  fof(f2,axiom,(
% 0.67/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f47,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.67/1.03    inference(cnf_transformation,[],[f2])).
% 0.67/1.03  
% 0.67/1.03  fof(f15,axiom,(
% 0.67/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f60,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.67/1.03    inference(cnf_transformation,[],[f15])).
% 0.67/1.03  
% 0.67/1.03  fof(f4,axiom,(
% 0.67/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f49,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f4])).
% 0.67/1.03  
% 0.67/1.03  fof(f5,axiom,(
% 0.67/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f50,plain,(
% 0.67/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f5])).
% 0.67/1.03  
% 0.67/1.03  fof(f6,axiom,(
% 0.67/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f51,plain,(
% 0.67/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f6])).
% 0.67/1.03  
% 0.67/1.03  fof(f7,axiom,(
% 0.67/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f52,plain,(
% 0.67/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f7])).
% 0.67/1.03  
% 0.67/1.03  fof(f8,axiom,(
% 0.67/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f53,plain,(
% 0.67/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f8])).
% 0.67/1.03  
% 0.67/1.03  fof(f9,axiom,(
% 0.67/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f54,plain,(
% 0.67/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f9])).
% 0.67/1.03  
% 0.67/1.03  fof(f73,plain,(
% 0.67/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.67/1.03    inference(definition_unfolding,[],[f53,f54])).
% 0.67/1.03  
% 0.67/1.03  fof(f74,plain,(
% 0.67/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.67/1.03    inference(definition_unfolding,[],[f52,f73])).
% 0.67/1.03  
% 0.67/1.03  fof(f75,plain,(
% 0.67/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.67/1.03    inference(definition_unfolding,[],[f51,f74])).
% 0.67/1.03  
% 0.67/1.03  fof(f76,plain,(
% 0.67/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.67/1.03    inference(definition_unfolding,[],[f50,f75])).
% 0.67/1.03  
% 0.67/1.03  fof(f77,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.67/1.03    inference(definition_unfolding,[],[f49,f76])).
% 0.67/1.03  
% 0.67/1.03  fof(f78,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.67/1.03    inference(definition_unfolding,[],[f60,f77])).
% 0.67/1.03  
% 0.67/1.03  fof(f79,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.67/1.03    inference(definition_unfolding,[],[f47,f78])).
% 0.67/1.03  
% 0.67/1.03  fof(f80,plain,(
% 0.67/1.03    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.67/1.03    inference(definition_unfolding,[],[f59,f79])).
% 0.67/1.03  
% 0.67/1.03  fof(f22,conjecture,(
% 0.67/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f23,negated_conjecture,(
% 0.67/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 0.67/1.03    inference(negated_conjecture,[],[f22])).
% 0.67/1.03  
% 0.67/1.03  fof(f39,plain,(
% 0.67/1.03    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.67/1.03    inference(ennf_transformation,[],[f23])).
% 0.67/1.03  
% 0.67/1.03  fof(f40,plain,(
% 0.67/1.03    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.67/1.03    inference(flattening,[],[f39])).
% 0.67/1.03  
% 0.67/1.03  fof(f41,plain,(
% 0.67/1.03    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.67/1.03    inference(nnf_transformation,[],[f40])).
% 0.67/1.03  
% 0.67/1.03  fof(f42,plain,(
% 0.67/1.03    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.67/1.03    inference(flattening,[],[f41])).
% 0.67/1.03  
% 0.67/1.03  fof(f44,plain,(
% 0.67/1.03    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.67/1.03    introduced(choice_axiom,[])).
% 0.67/1.03  
% 0.67/1.03  fof(f43,plain,(
% 0.67/1.03    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.67/1.03    introduced(choice_axiom,[])).
% 0.67/1.03  
% 0.67/1.03  fof(f45,plain,(
% 0.67/1.03    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.67/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 0.67/1.03  
% 0.67/1.03  fof(f70,plain,(
% 0.67/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.67/1.03    inference(cnf_transformation,[],[f45])).
% 0.67/1.03  
% 0.67/1.03  fof(f71,plain,(
% 0.67/1.03    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 0.67/1.03    inference(cnf_transformation,[],[f45])).
% 0.67/1.03  
% 0.67/1.03  fof(f17,axiom,(
% 0.67/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f31,plain,(
% 0.67/1.03    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.67/1.03    inference(ennf_transformation,[],[f17])).
% 0.67/1.03  
% 0.67/1.03  fof(f32,plain,(
% 0.67/1.03    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.67/1.03    inference(flattening,[],[f31])).
% 0.67/1.03  
% 0.67/1.03  fof(f62,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f32])).
% 0.67/1.03  
% 0.67/1.03  fof(f69,plain,(
% 0.67/1.03    l1_pre_topc(sK0)),
% 0.67/1.03    inference(cnf_transformation,[],[f45])).
% 0.67/1.03  
% 0.67/1.03  fof(f12,axiom,(
% 0.67/1.03    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f26,plain,(
% 0.67/1.03    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.67/1.03    inference(ennf_transformation,[],[f12])).
% 0.67/1.03  
% 0.67/1.03  fof(f57,plain,(
% 0.67/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.67/1.03    inference(cnf_transformation,[],[f26])).
% 0.67/1.03  
% 0.67/1.03  fof(f13,axiom,(
% 0.67/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f27,plain,(
% 0.67/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.67/1.03    inference(ennf_transformation,[],[f13])).
% 0.67/1.03  
% 0.67/1.03  fof(f28,plain,(
% 0.67/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.67/1.03    inference(flattening,[],[f27])).
% 0.67/1.03  
% 0.67/1.03  fof(f58,plain,(
% 0.67/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.67/1.03    inference(cnf_transformation,[],[f28])).
% 0.67/1.03  
% 0.67/1.03  fof(f1,axiom,(
% 0.67/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f46,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f1])).
% 0.67/1.03  
% 0.67/1.03  fof(f16,axiom,(
% 0.67/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f24,plain,(
% 0.67/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.67/1.03    inference(unused_predicate_definition_removal,[],[f16])).
% 0.67/1.03  
% 0.67/1.03  fof(f30,plain,(
% 0.67/1.03    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.67/1.03    inference(ennf_transformation,[],[f24])).
% 0.67/1.03  
% 0.67/1.03  fof(f61,plain,(
% 0.67/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.67/1.03    inference(cnf_transformation,[],[f30])).
% 0.67/1.03  
% 0.67/1.03  fof(f3,axiom,(
% 0.67/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f25,plain,(
% 0.67/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.67/1.03    inference(ennf_transformation,[],[f3])).
% 0.67/1.03  
% 0.67/1.03  fof(f48,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f25])).
% 0.67/1.03  
% 0.67/1.03  fof(f21,axiom,(
% 0.67/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f38,plain,(
% 0.67/1.03    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.67/1.03    inference(ennf_transformation,[],[f21])).
% 0.67/1.03  
% 0.67/1.03  fof(f67,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f38])).
% 0.67/1.03  
% 0.67/1.03  fof(f20,axiom,(
% 0.67/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 0.67/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.03  
% 0.67/1.03  fof(f37,plain,(
% 0.67/1.03    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.67/1.03    inference(ennf_transformation,[],[f20])).
% 0.67/1.03  
% 0.67/1.03  fof(f66,plain,(
% 0.67/1.03    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f37])).
% 0.67/1.03  
% 0.67/1.03  fof(f72,plain,(
% 0.67/1.03    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.67/1.03    inference(cnf_transformation,[],[f45])).
% 0.67/1.03  
% 0.67/1.03  fof(f63,plain,(
% 0.67/1.03    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.67/1.03    inference(cnf_transformation,[],[f32])).
% 0.67/1.03  
% 0.67/1.03  fof(f68,plain,(
% 0.67/1.03    v2_pre_topc(sK0)),
% 0.67/1.03    inference(cnf_transformation,[],[f45])).
% 0.67/1.03  
% 0.67/1.03  cnf(c_3,plain,
% 0.67/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 0.67/1.03      inference(cnf_transformation,[],[f56]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_858,plain,
% 0.67/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 0.67/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_2,plain,
% 0.67/1.03      ( k2_subset_1(X0) = X0 ),
% 0.67/1.03      inference(cnf_transformation,[],[f55]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_863,plain,
% 0.67/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 0.67/1.03      inference(light_normalisation,[status(thm)],[c_858,c_2]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_6,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.67/1.03      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 0.67/1.03      inference(cnf_transformation,[],[f80]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_855,plain,
% 0.67/1.03      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 0.67/1.03      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 0.67/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_2501,plain,
% 0.67/1.03      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_863,c_855]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_16,negated_conjecture,
% 0.67/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.67/1.03      inference(cnf_transformation,[],[f70]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_854,plain,
% 0.67/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.67/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_2499,plain,
% 0.67/1.03      ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_854,c_855]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_9237,plain,
% 0.67/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 0.67/1.03      inference(demodulation,[status(thm)],[c_2501,c_2499]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_15,negated_conjecture,
% 0.67/1.03      ( v4_pre_topc(sK1,sK0)
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 0.67/1.03      inference(cnf_transformation,[],[f71]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_138,plain,
% 0.67/1.03      ( v4_pre_topc(sK1,sK0)
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 0.67/1.03      inference(prop_impl,[status(thm)],[c_15]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_9,plain,
% 0.67/1.03      ( ~ v4_pre_topc(X0,X1)
% 0.67/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.67/1.03      | ~ l1_pre_topc(X1)
% 0.67/1.03      | k2_pre_topc(X1,X0) = X0 ),
% 0.67/1.03      inference(cnf_transformation,[],[f62]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_17,negated_conjecture,
% 0.67/1.03      ( l1_pre_topc(sK0) ),
% 0.67/1.03      inference(cnf_transformation,[],[f69]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_336,plain,
% 0.67/1.03      ( ~ v4_pre_topc(X0,X1)
% 0.67/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.67/1.03      | k2_pre_topc(X1,X0) = X0
% 0.67/1.03      | sK0 != X1 ),
% 0.67/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_337,plain,
% 0.67/1.03      ( ~ v4_pre_topc(X0,sK0)
% 0.67/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | k2_pre_topc(sK0,X0) = X0 ),
% 0.67/1.03      inference(unflattening,[status(thm)],[c_336]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_383,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 0.67/1.03      | k2_pre_topc(sK0,X0) = X0
% 0.67/1.03      | sK1 != X0
% 0.67/1.03      | sK0 != sK0 ),
% 0.67/1.03      inference(resolution_lifted,[status(thm)],[c_138,c_337]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_384,plain,
% 0.67/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 0.67/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 0.67/1.03      inference(unflattening,[status(thm)],[c_383]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_386,plain,
% 0.67/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 0.67/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 0.67/1.03      inference(global_propositional_subsumption,
% 0.67/1.03                [status(thm)],
% 0.67/1.03                [c_384,c_16]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_477,plain,
% 0.67/1.03      ( k2_pre_topc(sK0,sK1) = sK1
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 0.67/1.03      inference(prop_impl,[status(thm)],[c_386]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_478,plain,
% 0.67/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 0.67/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 0.67/1.03      inference(renaming,[status(thm)],[c_477]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_9341,plain,
% 0.67/1.03      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 0.67/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_9237,c_478]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_4,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.67/1.03      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 0.67/1.03      inference(cnf_transformation,[],[f57]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_857,plain,
% 0.67/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.67/1.03      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 0.67/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_5,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.67/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 0.67/1.03      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 0.67/1.03      inference(cnf_transformation,[],[f58]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_856,plain,
% 0.67/1.03      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 0.67/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 0.67/1.03      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 0.67/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_2225,plain,
% 0.67/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 0.67/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_854,c_856]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_2518,plain,
% 0.67/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),X0,X1)) = k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),X0,X1))
% 0.67/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_857,c_2225]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_4929,plain,
% 0.67/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k2_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_854,c_2518]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_9304,plain,
% 0.67/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X0)) = k2_xboole_0(sK1,k7_subset_1(sK1,sK1,X0)) ),
% 0.67/1.03      inference(demodulation,[status(thm)],[c_9237,c_4929]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_0,plain,
% 0.67/1.03      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 0.67/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_7,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.67/1.03      inference(cnf_transformation,[],[f61]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_1,plain,
% 0.67/1.03      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 0.67/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_240,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1 ),
% 0.67/1.03      inference(resolution,[status(thm)],[c_7,c_1]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_853,plain,
% 0.67/1.03      ( k2_xboole_0(X0,X1) = X1
% 0.67/1.03      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 0.67/1.03      inference(predicate_to_equality,[status(thm)],[c_240]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_3280,plain,
% 0.67/1.03      ( k2_xboole_0(k7_subset_1(X0,X1,X2),X0) = X0
% 0.67/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_857,c_853]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_5942,plain,
% 0.67/1.03      ( k2_xboole_0(k7_subset_1(X0,X0,X1),X0) = X0 ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_863,c_3280]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_6937,plain,
% 0.67/1.03      ( k2_xboole_0(X0,k7_subset_1(X0,X0,X1)) = X0 ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_0,c_5942]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_9306,plain,
% 0.67/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X0)) = sK1 ),
% 0.67/1.03      inference(demodulation,[status(thm)],[c_9304,c_6937]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_9671,plain,
% 0.67/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = sK1
% 0.67/1.03      | k2_pre_topc(sK0,sK1) = sK1 ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_9341,c_9306]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_13,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.67/1.03      | ~ l1_pre_topc(X1)
% 0.67/1.03      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 0.67/1.03      inference(cnf_transformation,[],[f67]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_300,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.67/1.03      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 0.67/1.03      | sK0 != X1 ),
% 0.67/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_301,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 0.67/1.03      inference(unflattening,[status(thm)],[c_300]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_852,plain,
% 0.67/1.03      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 0.67/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.67/1.03      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_1029,plain,
% 0.67/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_854,c_852]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_9690,plain,
% 0.67/1.03      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 0.67/1.03      inference(demodulation,[status(thm)],[c_9671,c_1029]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_12,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.67/1.03      | ~ l1_pre_topc(X1)
% 0.67/1.03      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 0.67/1.03      inference(cnf_transformation,[],[f66]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_312,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.67/1.03      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 0.67/1.03      | sK0 != X1 ),
% 0.67/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_313,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 0.67/1.03      inference(unflattening,[status(thm)],[c_312]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_851,plain,
% 0.67/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 0.67/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.67/1.03      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_1064,plain,
% 0.67/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 0.67/1.03      inference(superposition,[status(thm)],[c_854,c_851]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_9723,plain,
% 0.67/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 0.67/1.03      inference(demodulation,[status(thm)],[c_9690,c_1064]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_14,negated_conjecture,
% 0.67/1.03      ( ~ v4_pre_topc(sK1,sK0)
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 0.67/1.03      inference(cnf_transformation,[],[f72]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_136,plain,
% 0.67/1.03      ( ~ v4_pre_topc(sK1,sK0)
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 0.67/1.03      inference(prop_impl,[status(thm)],[c_14]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_8,plain,
% 0.67/1.03      ( v4_pre_topc(X0,X1)
% 0.67/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.67/1.03      | ~ l1_pre_topc(X1)
% 0.67/1.03      | ~ v2_pre_topc(X1)
% 0.67/1.03      | k2_pre_topc(X1,X0) != X0 ),
% 0.67/1.03      inference(cnf_transformation,[],[f63]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_18,negated_conjecture,
% 0.67/1.03      ( v2_pre_topc(sK0) ),
% 0.67/1.03      inference(cnf_transformation,[],[f68]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_272,plain,
% 0.67/1.03      ( v4_pre_topc(X0,X1)
% 0.67/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.67/1.03      | ~ l1_pre_topc(X1)
% 0.67/1.03      | k2_pre_topc(X1,X0) != X0
% 0.67/1.03      | sK0 != X1 ),
% 0.67/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_273,plain,
% 0.67/1.03      ( v4_pre_topc(X0,sK0)
% 0.67/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | ~ l1_pre_topc(sK0)
% 0.67/1.03      | k2_pre_topc(sK0,X0) != X0 ),
% 0.67/1.03      inference(unflattening,[status(thm)],[c_272]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_277,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | v4_pre_topc(X0,sK0)
% 0.67/1.03      | k2_pre_topc(sK0,X0) != X0 ),
% 0.67/1.03      inference(global_propositional_subsumption,
% 0.67/1.03                [status(thm)],
% 0.67/1.03                [c_273,c_17]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_278,plain,
% 0.67/1.03      ( v4_pre_topc(X0,sK0)
% 0.67/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | k2_pre_topc(sK0,X0) != X0 ),
% 0.67/1.03      inference(renaming,[status(thm)],[c_277]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_394,plain,
% 0.67/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 0.67/1.03      | k2_pre_topc(sK0,X0) != X0
% 0.67/1.03      | sK1 != X0
% 0.67/1.03      | sK0 != sK0 ),
% 0.67/1.03      inference(resolution_lifted,[status(thm)],[c_136,c_278]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_395,plain,
% 0.67/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.67/1.03      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 0.67/1.03      | k2_pre_topc(sK0,sK1) != sK1 ),
% 0.67/1.03      inference(unflattening,[status(thm)],[c_394]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(c_397,plain,
% 0.67/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 0.67/1.03      | k2_pre_topc(sK0,sK1) != sK1 ),
% 0.67/1.03      inference(global_propositional_subsumption,
% 0.67/1.03                [status(thm)],
% 0.67/1.03                [c_395,c_16]) ).
% 0.67/1.03  
% 0.67/1.03  cnf(contradiction,plain,
% 0.67/1.03      ( $false ),
% 0.67/1.03      inference(minisat,[status(thm)],[c_9723,c_9690,c_397]) ).
% 0.67/1.03  
% 0.67/1.03  
% 0.67/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.67/1.03  
% 0.67/1.03  ------                               Statistics
% 0.67/1.03  
% 0.67/1.03  ------ General
% 0.67/1.03  
% 0.67/1.03  abstr_ref_over_cycles:                  0
% 0.67/1.03  abstr_ref_under_cycles:                 0
% 0.67/1.03  gc_basic_clause_elim:                   0
% 0.67/1.03  forced_gc_time:                         0
% 0.67/1.03  parsing_time:                           0.011
% 0.67/1.03  unif_index_cands_time:                  0.
% 0.67/1.03  unif_index_add_time:                    0.
% 0.67/1.03  orderings_time:                         0.
% 0.67/1.03  out_proof_time:                         0.01
% 0.67/1.03  total_time:                             0.31
% 0.67/1.03  num_of_symbols:                         50
% 0.67/1.03  num_of_terms:                           11090
% 0.67/1.03  
% 0.67/1.03  ------ Preprocessing
% 0.67/1.03  
% 0.67/1.03  num_of_splits:                          0
% 0.67/1.03  num_of_split_atoms:                     0
% 0.67/1.03  num_of_reused_defs:                     0
% 0.67/1.03  num_eq_ax_congr_red:                    43
% 0.67/1.03  num_of_sem_filtered_clauses:            1
% 0.67/1.03  num_of_subtypes:                        0
% 0.67/1.03  monotx_restored_types:                  0
% 0.67/1.03  sat_num_of_epr_types:                   0
% 0.67/1.03  sat_num_of_non_cyclic_types:            0
% 0.67/1.03  sat_guarded_non_collapsed_types:        0
% 0.67/1.03  num_pure_diseq_elim:                    0
% 0.67/1.03  simp_replaced_by:                       0
% 0.67/1.03  res_preprocessed:                       89
% 0.67/1.03  prep_upred:                             0
% 0.67/1.03  prep_unflattend:                        9
% 0.67/1.03  smt_new_axioms:                         0
% 0.67/1.03  pred_elim_cands:                        1
% 0.67/1.03  pred_elim:                              4
% 0.67/1.03  pred_elim_cl:                           4
% 0.67/1.03  pred_elim_cycles:                       6
% 0.67/1.03  merged_defs:                            8
% 0.67/1.03  merged_defs_ncl:                        0
% 0.67/1.03  bin_hyper_res:                          9
% 0.67/1.03  prep_cycles:                            4
% 0.67/1.03  pred_elim_time:                         0.004
% 0.67/1.03  splitting_time:                         0.
% 0.67/1.03  sem_filter_time:                        0.
% 0.67/1.03  monotx_time:                            0.
% 0.67/1.03  subtype_inf_time:                       0.
% 0.67/1.03  
% 0.67/1.03  ------ Problem properties
% 0.67/1.03  
% 0.67/1.03  clauses:                                15
% 0.67/1.03  conjectures:                            1
% 0.67/1.03  epr:                                    0
% 0.67/1.03  horn:                                   14
% 0.67/1.03  ground:                                 3
% 0.67/1.03  unary:                                  4
% 0.67/1.03  binary:                                 8
% 0.67/1.03  lits:                                   29
% 0.67/1.03  lits_eq:                                14
% 0.67/1.03  fd_pure:                                0
% 0.67/1.03  fd_pseudo:                              0
% 0.67/1.03  fd_cond:                                0
% 0.67/1.03  fd_pseudo_cond:                         0
% 0.67/1.03  ac_symbols:                             0
% 0.67/1.03  
% 0.67/1.03  ------ Propositional Solver
% 0.67/1.03  
% 0.67/1.03  prop_solver_calls:                      29
% 0.67/1.03  prop_fast_solver_calls:                 613
% 0.67/1.03  smt_solver_calls:                       0
% 0.67/1.03  smt_fast_solver_calls:                  0
% 0.67/1.03  prop_num_of_clauses:                    4610
% 0.67/1.03  prop_preprocess_simplified:             9337
% 0.67/1.03  prop_fo_subsumed:                       8
% 0.67/1.03  prop_solver_time:                       0.
% 0.67/1.03  smt_solver_time:                        0.
% 0.67/1.03  smt_fast_solver_time:                   0.
% 0.67/1.03  prop_fast_solver_time:                  0.
% 0.67/1.03  prop_unsat_core_time:                   0.
% 0.67/1.03  
% 0.67/1.03  ------ QBF
% 0.67/1.03  
% 0.67/1.03  qbf_q_res:                              0
% 0.67/1.03  qbf_num_tautologies:                    0
% 0.67/1.03  qbf_prep_cycles:                        0
% 0.67/1.03  
% 0.67/1.03  ------ BMC1
% 0.67/1.03  
% 0.67/1.03  bmc1_current_bound:                     -1
% 0.67/1.03  bmc1_last_solved_bound:                 -1
% 0.67/1.03  bmc1_unsat_core_size:                   -1
% 0.67/1.03  bmc1_unsat_core_parents_size:           -1
% 0.67/1.03  bmc1_merge_next_fun:                    0
% 0.67/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.67/1.03  
% 0.67/1.03  ------ Instantiation
% 0.67/1.03  
% 0.67/1.03  inst_num_of_clauses:                    1191
% 0.67/1.03  inst_num_in_passive:                    457
% 0.67/1.03  inst_num_in_active:                     570
% 0.67/1.03  inst_num_in_unprocessed:                164
% 0.67/1.03  inst_num_of_loops:                      590
% 0.67/1.03  inst_num_of_learning_restarts:          0
% 0.67/1.03  inst_num_moves_active_passive:          18
% 0.67/1.03  inst_lit_activity:                      0
% 0.67/1.03  inst_lit_activity_moves:                1
% 0.67/1.03  inst_num_tautologies:                   0
% 0.67/1.03  inst_num_prop_implied:                  0
% 0.67/1.03  inst_num_existing_simplified:           0
% 0.67/1.03  inst_num_eq_res_simplified:             0
% 0.67/1.03  inst_num_child_elim:                    0
% 0.67/1.03  inst_num_of_dismatching_blockings:      617
% 0.67/1.03  inst_num_of_non_proper_insts:           866
% 0.67/1.03  inst_num_of_duplicates:                 0
% 0.67/1.03  inst_inst_num_from_inst_to_res:         0
% 0.67/1.03  inst_dismatching_checking_time:         0.
% 0.67/1.03  
% 0.67/1.03  ------ Resolution
% 0.67/1.03  
% 0.67/1.03  res_num_of_clauses:                     0
% 0.67/1.03  res_num_in_passive:                     0
% 0.67/1.03  res_num_in_active:                      0
% 0.67/1.03  res_num_of_loops:                       93
% 0.67/1.03  res_forward_subset_subsumed:            16
% 0.67/1.03  res_backward_subset_subsumed:           2
% 0.67/1.03  res_forward_subsumed:                   0
% 0.67/1.03  res_backward_subsumed:                  0
% 0.67/1.03  res_forward_subsumption_resolution:     0
% 0.67/1.03  res_backward_subsumption_resolution:    0
% 0.67/1.03  res_clause_to_clause_subsumption:       1442
% 0.67/1.03  res_orphan_elimination:                 0
% 0.67/1.03  res_tautology_del:                      50
% 0.67/1.03  res_num_eq_res_simplified:              1
% 0.67/1.03  res_num_sel_changes:                    0
% 0.67/1.03  res_moves_from_active_to_pass:          0
% 0.67/1.03  
% 0.67/1.03  ------ Superposition
% 0.67/1.03  
% 0.67/1.03  sup_time_total:                         0.
% 0.67/1.03  sup_time_generating:                    0.
% 0.67/1.03  sup_time_sim_full:                      0.
% 0.67/1.03  sup_time_sim_immed:                     0.
% 0.67/1.03  
% 0.67/1.03  sup_num_of_clauses:                     292
% 0.67/1.03  sup_num_in_active:                      95
% 0.67/1.03  sup_num_in_passive:                     197
% 0.67/1.03  sup_num_of_loops:                       116
% 0.67/1.03  sup_fw_superposition:                   311
% 0.67/1.03  sup_bw_superposition:                   126
% 0.67/1.03  sup_immediate_simplified:               21
% 0.67/1.03  sup_given_eliminated:                   2
% 0.67/1.03  comparisons_done:                       0
% 0.67/1.03  comparisons_avoided:                    9
% 0.67/1.03  
% 0.67/1.03  ------ Simplifications
% 0.67/1.03  
% 0.67/1.03  
% 0.67/1.03  sim_fw_subset_subsumed:                 9
% 0.67/1.03  sim_bw_subset_subsumed:                 4
% 0.67/1.03  sim_fw_subsumed:                        1
% 0.67/1.03  sim_bw_subsumed:                        3
% 0.67/1.03  sim_fw_subsumption_res:                 0
% 0.67/1.03  sim_bw_subsumption_res:                 0
% 0.67/1.03  sim_tautology_del:                      1
% 0.67/1.03  sim_eq_tautology_del:                   2
% 0.67/1.03  sim_eq_res_simp:                        0
% 0.67/1.03  sim_fw_demodulated:                     2
% 0.67/1.03  sim_bw_demodulated:                     18
% 0.67/1.03  sim_light_normalised:                   13
% 0.67/1.03  sim_joinable_taut:                      0
% 0.67/1.03  sim_joinable_simp:                      0
% 0.67/1.03  sim_ac_normalised:                      0
% 0.67/1.03  sim_smt_subsumption:                    0
% 0.67/1.03  
%------------------------------------------------------------------------------

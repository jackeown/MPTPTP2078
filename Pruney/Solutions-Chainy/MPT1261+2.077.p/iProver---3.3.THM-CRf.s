%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:35 EST 2020

% Result     : Theorem 31.87s
% Output     : CNFRefutation 31.87s
% Verified   : 
% Statistics : Number of formulae       :  182 (1901 expanded)
%              Number of clauses        :  113 ( 594 expanded)
%              Number of leaves         :   21 ( 445 expanded)
%              Depth                    :   26
%              Number of atoms          :  411 (6428 expanded)
%              Number of equality atoms :  207 (2479 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

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

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f31])).

cnf(c_8,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1111,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1112,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1115,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1112,c_11])).

cnf(c_4719,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1111,c_1115])).

cnf(c_12046,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_4719])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1109,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5842,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1108,c_1109])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_1107,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_1264,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1108,c_1107])).

cnf(c_6458,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5842,c_1264])).

cnf(c_1996,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11,c_11])).

cnf(c_4799,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_8,c_1996])).

cnf(c_4828,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_4799,c_11])).

cnf(c_6887,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)))) = k4_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_6458,c_4828])).

cnf(c_6896,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)))) = k1_setfam_1(k2_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) ),
    inference(demodulation,[status(thm)],[c_6887,c_1996])).

cnf(c_12171,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_12046,c_6896])).

cnf(c_19,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_139,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_376,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_377,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_139,c_377])).

cnf(c_473,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_475,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_20])).

cnf(c_629,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_475])).

cnf(c_630,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_629])).

cnf(c_6457,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5842,c_630])).

cnf(c_7715,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6457,c_1111])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_337,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_338,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,X0),X0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_139,c_338])).

cnf(c_484,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_486,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_20])).

cnf(c_18,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_137,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_242,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_243,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_21])).

cnf(c_248,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_137,c_248])).

cnf(c_498,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_500,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_20])).

cnf(c_627,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_500])).

cnf(c_628,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(renaming,[status(thm)],[c_627])).

cnf(c_659,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(bin_hyper_res,[status(thm)],[c_486,c_628])).

cnf(c_667,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_17696,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7715,c_667])).

cnf(c_17700,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_17696,c_1115])).

cnf(c_2035,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1111])).

cnf(c_4720,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2035,c_1115])).

cnf(c_13611,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_4720])).

cnf(c_14420,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_13611,c_4720])).

cnf(c_12075,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4719,c_4799])).

cnf(c_12078,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_12075,c_11])).

cnf(c_14424,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_13611,c_12078])).

cnf(c_14438,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_14424,c_13611])).

cnf(c_14440,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_14420,c_13611,c_14438])).

cnf(c_18632,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_17700,c_14440])).

cnf(c_21531,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_12171,c_12171,c_17700,c_18632])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1114,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_11])).

cnf(c_12070,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_4719,c_1114])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1113,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4712,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1111,c_1113])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8223,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4712,c_3])).

cnf(c_8596,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8223,c_11])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1995,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7,c_11])).

cnf(c_2471,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_8,c_1995])).

cnf(c_8637,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8596,c_2471])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1997,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_3231,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1997,c_1114])).

cnf(c_9201,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8637,c_3231])).

cnf(c_12080,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12070,c_9201])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_105049,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12080,c_6])).

cnf(c_105051,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_105049,c_3])).

cnf(c_106996,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_21531,c_105051])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_1105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1110,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7525,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_1110])).

cnf(c_7590,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_7525])).

cnf(c_7629,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1108,c_7590])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_1106,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_1212,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1108,c_1106])).

cnf(c_7631,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_7629,c_1212])).

cnf(c_109061,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_106996,c_7631])).

cnf(c_6454,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5842,c_628])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109061,c_21531,c_6454])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:06:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.87/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.87/4.49  
% 31.87/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.87/4.49  
% 31.87/4.49  ------  iProver source info
% 31.87/4.49  
% 31.87/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.87/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.87/4.49  git: non_committed_changes: false
% 31.87/4.49  git: last_make_outside_of_git: false
% 31.87/4.49  
% 31.87/4.49  ------ 
% 31.87/4.49  
% 31.87/4.49  ------ Input Options
% 31.87/4.49  
% 31.87/4.49  --out_options                           all
% 31.87/4.49  --tptp_safe_out                         true
% 31.87/4.49  --problem_path                          ""
% 31.87/4.49  --include_path                          ""
% 31.87/4.49  --clausifier                            res/vclausify_rel
% 31.87/4.49  --clausifier_options                    ""
% 31.87/4.49  --stdin                                 false
% 31.87/4.49  --stats_out                             all
% 31.87/4.49  
% 31.87/4.49  ------ General Options
% 31.87/4.49  
% 31.87/4.49  --fof                                   false
% 31.87/4.49  --time_out_real                         305.
% 31.87/4.49  --time_out_virtual                      -1.
% 31.87/4.49  --symbol_type_check                     false
% 31.87/4.49  --clausify_out                          false
% 31.87/4.49  --sig_cnt_out                           false
% 31.87/4.49  --trig_cnt_out                          false
% 31.87/4.49  --trig_cnt_out_tolerance                1.
% 31.87/4.49  --trig_cnt_out_sk_spl                   false
% 31.87/4.49  --abstr_cl_out                          false
% 31.87/4.49  
% 31.87/4.49  ------ Global Options
% 31.87/4.49  
% 31.87/4.49  --schedule                              default
% 31.87/4.49  --add_important_lit                     false
% 31.87/4.49  --prop_solver_per_cl                    1000
% 31.87/4.49  --min_unsat_core                        false
% 31.87/4.49  --soft_assumptions                      false
% 31.87/4.49  --soft_lemma_size                       3
% 31.87/4.49  --prop_impl_unit_size                   0
% 31.87/4.49  --prop_impl_unit                        []
% 31.87/4.49  --share_sel_clauses                     true
% 31.87/4.49  --reset_solvers                         false
% 31.87/4.49  --bc_imp_inh                            [conj_cone]
% 31.87/4.49  --conj_cone_tolerance                   3.
% 31.87/4.49  --extra_neg_conj                        none
% 31.87/4.49  --large_theory_mode                     true
% 31.87/4.49  --prolific_symb_bound                   200
% 31.87/4.49  --lt_threshold                          2000
% 31.87/4.49  --clause_weak_htbl                      true
% 31.87/4.49  --gc_record_bc_elim                     false
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing Options
% 31.87/4.49  
% 31.87/4.49  --preprocessing_flag                    true
% 31.87/4.49  --time_out_prep_mult                    0.1
% 31.87/4.49  --splitting_mode                        input
% 31.87/4.49  --splitting_grd                         true
% 31.87/4.49  --splitting_cvd                         false
% 31.87/4.49  --splitting_cvd_svl                     false
% 31.87/4.49  --splitting_nvd                         32
% 31.87/4.49  --sub_typing                            true
% 31.87/4.49  --prep_gs_sim                           true
% 31.87/4.49  --prep_unflatten                        true
% 31.87/4.49  --prep_res_sim                          true
% 31.87/4.49  --prep_upred                            true
% 31.87/4.49  --prep_sem_filter                       exhaustive
% 31.87/4.49  --prep_sem_filter_out                   false
% 31.87/4.49  --pred_elim                             true
% 31.87/4.49  --res_sim_input                         true
% 31.87/4.49  --eq_ax_congr_red                       true
% 31.87/4.49  --pure_diseq_elim                       true
% 31.87/4.49  --brand_transform                       false
% 31.87/4.49  --non_eq_to_eq                          false
% 31.87/4.49  --prep_def_merge                        true
% 31.87/4.49  --prep_def_merge_prop_impl              false
% 31.87/4.49  --prep_def_merge_mbd                    true
% 31.87/4.49  --prep_def_merge_tr_red                 false
% 31.87/4.49  --prep_def_merge_tr_cl                  false
% 31.87/4.49  --smt_preprocessing                     true
% 31.87/4.49  --smt_ac_axioms                         fast
% 31.87/4.49  --preprocessed_out                      false
% 31.87/4.49  --preprocessed_stats                    false
% 31.87/4.49  
% 31.87/4.49  ------ Abstraction refinement Options
% 31.87/4.49  
% 31.87/4.49  --abstr_ref                             []
% 31.87/4.49  --abstr_ref_prep                        false
% 31.87/4.49  --abstr_ref_until_sat                   false
% 31.87/4.49  --abstr_ref_sig_restrict                funpre
% 31.87/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.87/4.49  --abstr_ref_under                       []
% 31.87/4.49  
% 31.87/4.49  ------ SAT Options
% 31.87/4.49  
% 31.87/4.49  --sat_mode                              false
% 31.87/4.49  --sat_fm_restart_options                ""
% 31.87/4.49  --sat_gr_def                            false
% 31.87/4.49  --sat_epr_types                         true
% 31.87/4.49  --sat_non_cyclic_types                  false
% 31.87/4.49  --sat_finite_models                     false
% 31.87/4.49  --sat_fm_lemmas                         false
% 31.87/4.49  --sat_fm_prep                           false
% 31.87/4.49  --sat_fm_uc_incr                        true
% 31.87/4.49  --sat_out_model                         small
% 31.87/4.49  --sat_out_clauses                       false
% 31.87/4.49  
% 31.87/4.49  ------ QBF Options
% 31.87/4.49  
% 31.87/4.49  --qbf_mode                              false
% 31.87/4.49  --qbf_elim_univ                         false
% 31.87/4.49  --qbf_dom_inst                          none
% 31.87/4.49  --qbf_dom_pre_inst                      false
% 31.87/4.49  --qbf_sk_in                             false
% 31.87/4.49  --qbf_pred_elim                         true
% 31.87/4.49  --qbf_split                             512
% 31.87/4.49  
% 31.87/4.49  ------ BMC1 Options
% 31.87/4.49  
% 31.87/4.49  --bmc1_incremental                      false
% 31.87/4.49  --bmc1_axioms                           reachable_all
% 31.87/4.49  --bmc1_min_bound                        0
% 31.87/4.49  --bmc1_max_bound                        -1
% 31.87/4.49  --bmc1_max_bound_default                -1
% 31.87/4.49  --bmc1_symbol_reachability              true
% 31.87/4.49  --bmc1_property_lemmas                  false
% 31.87/4.49  --bmc1_k_induction                      false
% 31.87/4.49  --bmc1_non_equiv_states                 false
% 31.87/4.49  --bmc1_deadlock                         false
% 31.87/4.49  --bmc1_ucm                              false
% 31.87/4.49  --bmc1_add_unsat_core                   none
% 31.87/4.49  --bmc1_unsat_core_children              false
% 31.87/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.87/4.49  --bmc1_out_stat                         full
% 31.87/4.49  --bmc1_ground_init                      false
% 31.87/4.49  --bmc1_pre_inst_next_state              false
% 31.87/4.49  --bmc1_pre_inst_state                   false
% 31.87/4.49  --bmc1_pre_inst_reach_state             false
% 31.87/4.49  --bmc1_out_unsat_core                   false
% 31.87/4.49  --bmc1_aig_witness_out                  false
% 31.87/4.49  --bmc1_verbose                          false
% 31.87/4.49  --bmc1_dump_clauses_tptp                false
% 31.87/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.87/4.49  --bmc1_dump_file                        -
% 31.87/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.87/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.87/4.49  --bmc1_ucm_extend_mode                  1
% 31.87/4.49  --bmc1_ucm_init_mode                    2
% 31.87/4.49  --bmc1_ucm_cone_mode                    none
% 31.87/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.87/4.49  --bmc1_ucm_relax_model                  4
% 31.87/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.87/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.87/4.49  --bmc1_ucm_layered_model                none
% 31.87/4.49  --bmc1_ucm_max_lemma_size               10
% 31.87/4.49  
% 31.87/4.49  ------ AIG Options
% 31.87/4.49  
% 31.87/4.49  --aig_mode                              false
% 31.87/4.49  
% 31.87/4.49  ------ Instantiation Options
% 31.87/4.49  
% 31.87/4.49  --instantiation_flag                    true
% 31.87/4.49  --inst_sos_flag                         true
% 31.87/4.49  --inst_sos_phase                        true
% 31.87/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.87/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.87/4.49  --inst_lit_sel_side                     num_symb
% 31.87/4.49  --inst_solver_per_active                1400
% 31.87/4.49  --inst_solver_calls_frac                1.
% 31.87/4.49  --inst_passive_queue_type               priority_queues
% 31.87/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.87/4.49  --inst_passive_queues_freq              [25;2]
% 31.87/4.49  --inst_dismatching                      true
% 31.87/4.49  --inst_eager_unprocessed_to_passive     true
% 31.87/4.49  --inst_prop_sim_given                   true
% 31.87/4.49  --inst_prop_sim_new                     false
% 31.87/4.49  --inst_subs_new                         false
% 31.87/4.49  --inst_eq_res_simp                      false
% 31.87/4.49  --inst_subs_given                       false
% 31.87/4.49  --inst_orphan_elimination               true
% 31.87/4.49  --inst_learning_loop_flag               true
% 31.87/4.49  --inst_learning_start                   3000
% 31.87/4.49  --inst_learning_factor                  2
% 31.87/4.49  --inst_start_prop_sim_after_learn       3
% 31.87/4.49  --inst_sel_renew                        solver
% 31.87/4.49  --inst_lit_activity_flag                true
% 31.87/4.49  --inst_restr_to_given                   false
% 31.87/4.49  --inst_activity_threshold               500
% 31.87/4.49  --inst_out_proof                        true
% 31.87/4.49  
% 31.87/4.49  ------ Resolution Options
% 31.87/4.49  
% 31.87/4.49  --resolution_flag                       true
% 31.87/4.49  --res_lit_sel                           adaptive
% 31.87/4.49  --res_lit_sel_side                      none
% 31.87/4.49  --res_ordering                          kbo
% 31.87/4.49  --res_to_prop_solver                    active
% 31.87/4.49  --res_prop_simpl_new                    false
% 31.87/4.49  --res_prop_simpl_given                  true
% 31.87/4.49  --res_passive_queue_type                priority_queues
% 31.87/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.87/4.49  --res_passive_queues_freq               [15;5]
% 31.87/4.49  --res_forward_subs                      full
% 31.87/4.49  --res_backward_subs                     full
% 31.87/4.49  --res_forward_subs_resolution           true
% 31.87/4.49  --res_backward_subs_resolution          true
% 31.87/4.49  --res_orphan_elimination                true
% 31.87/4.49  --res_time_limit                        2.
% 31.87/4.49  --res_out_proof                         true
% 31.87/4.49  
% 31.87/4.49  ------ Superposition Options
% 31.87/4.49  
% 31.87/4.49  --superposition_flag                    true
% 31.87/4.49  --sup_passive_queue_type                priority_queues
% 31.87/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.87/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.87/4.49  --demod_completeness_check              fast
% 31.87/4.49  --demod_use_ground                      true
% 31.87/4.49  --sup_to_prop_solver                    passive
% 31.87/4.49  --sup_prop_simpl_new                    true
% 31.87/4.49  --sup_prop_simpl_given                  true
% 31.87/4.49  --sup_fun_splitting                     true
% 31.87/4.49  --sup_smt_interval                      50000
% 31.87/4.49  
% 31.87/4.49  ------ Superposition Simplification Setup
% 31.87/4.49  
% 31.87/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.87/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.87/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.87/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.87/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.87/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.87/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.87/4.49  --sup_immed_triv                        [TrivRules]
% 31.87/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.87/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.87/4.49  --sup_immed_bw_main                     []
% 31.87/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.87/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.87/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.87/4.49  --sup_input_bw                          []
% 31.87/4.49  
% 31.87/4.49  ------ Combination Options
% 31.87/4.49  
% 31.87/4.49  --comb_res_mult                         3
% 31.87/4.49  --comb_sup_mult                         2
% 31.87/4.49  --comb_inst_mult                        10
% 31.87/4.49  
% 31.87/4.49  ------ Debug Options
% 31.87/4.49  
% 31.87/4.49  --dbg_backtrace                         false
% 31.87/4.49  --dbg_dump_prop_clauses                 false
% 31.87/4.49  --dbg_dump_prop_clauses_file            -
% 31.87/4.49  --dbg_out_stat                          false
% 31.87/4.49  ------ Parsing...
% 31.87/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  ------ Proving...
% 31.87/4.49  ------ Problem Properties 
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  clauses                                 20
% 31.87/4.49  conjectures                             1
% 31.87/4.49  EPR                                     0
% 31.87/4.49  Horn                                    19
% 31.87/4.49  unary                                   9
% 31.87/4.49  binary                                  9
% 31.87/4.49  lits                                    33
% 31.87/4.49  lits eq                                 19
% 31.87/4.49  fd_pure                                 0
% 31.87/4.49  fd_pseudo                               0
% 31.87/4.49  fd_cond                                 0
% 31.87/4.49  fd_pseudo_cond                          0
% 31.87/4.49  AC symbols                              0
% 31.87/4.49  
% 31.87/4.49  ------ Schedule dynamic 5 is on 
% 31.87/4.49  
% 31.87/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ 
% 31.87/4.49  Current options:
% 31.87/4.49  ------ 
% 31.87/4.49  
% 31.87/4.49  ------ Input Options
% 31.87/4.49  
% 31.87/4.49  --out_options                           all
% 31.87/4.49  --tptp_safe_out                         true
% 31.87/4.49  --problem_path                          ""
% 31.87/4.49  --include_path                          ""
% 31.87/4.49  --clausifier                            res/vclausify_rel
% 31.87/4.49  --clausifier_options                    ""
% 31.87/4.49  --stdin                                 false
% 31.87/4.49  --stats_out                             all
% 31.87/4.49  
% 31.87/4.49  ------ General Options
% 31.87/4.49  
% 31.87/4.49  --fof                                   false
% 31.87/4.49  --time_out_real                         305.
% 31.87/4.49  --time_out_virtual                      -1.
% 31.87/4.49  --symbol_type_check                     false
% 31.87/4.49  --clausify_out                          false
% 31.87/4.49  --sig_cnt_out                           false
% 31.87/4.49  --trig_cnt_out                          false
% 31.87/4.49  --trig_cnt_out_tolerance                1.
% 31.87/4.49  --trig_cnt_out_sk_spl                   false
% 31.87/4.49  --abstr_cl_out                          false
% 31.87/4.49  
% 31.87/4.49  ------ Global Options
% 31.87/4.49  
% 31.87/4.49  --schedule                              default
% 31.87/4.49  --add_important_lit                     false
% 31.87/4.49  --prop_solver_per_cl                    1000
% 31.87/4.49  --min_unsat_core                        false
% 31.87/4.49  --soft_assumptions                      false
% 31.87/4.49  --soft_lemma_size                       3
% 31.87/4.49  --prop_impl_unit_size                   0
% 31.87/4.49  --prop_impl_unit                        []
% 31.87/4.49  --share_sel_clauses                     true
% 31.87/4.49  --reset_solvers                         false
% 31.87/4.49  --bc_imp_inh                            [conj_cone]
% 31.87/4.49  --conj_cone_tolerance                   3.
% 31.87/4.49  --extra_neg_conj                        none
% 31.87/4.49  --large_theory_mode                     true
% 31.87/4.49  --prolific_symb_bound                   200
% 31.87/4.49  --lt_threshold                          2000
% 31.87/4.49  --clause_weak_htbl                      true
% 31.87/4.49  --gc_record_bc_elim                     false
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing Options
% 31.87/4.49  
% 31.87/4.49  --preprocessing_flag                    true
% 31.87/4.49  --time_out_prep_mult                    0.1
% 31.87/4.49  --splitting_mode                        input
% 31.87/4.49  --splitting_grd                         true
% 31.87/4.49  --splitting_cvd                         false
% 31.87/4.49  --splitting_cvd_svl                     false
% 31.87/4.49  --splitting_nvd                         32
% 31.87/4.49  --sub_typing                            true
% 31.87/4.49  --prep_gs_sim                           true
% 31.87/4.49  --prep_unflatten                        true
% 31.87/4.49  --prep_res_sim                          true
% 31.87/4.49  --prep_upred                            true
% 31.87/4.49  --prep_sem_filter                       exhaustive
% 31.87/4.49  --prep_sem_filter_out                   false
% 31.87/4.49  --pred_elim                             true
% 31.87/4.49  --res_sim_input                         true
% 31.87/4.49  --eq_ax_congr_red                       true
% 31.87/4.49  --pure_diseq_elim                       true
% 31.87/4.49  --brand_transform                       false
% 31.87/4.49  --non_eq_to_eq                          false
% 31.87/4.49  --prep_def_merge                        true
% 31.87/4.49  --prep_def_merge_prop_impl              false
% 31.87/4.49  --prep_def_merge_mbd                    true
% 31.87/4.49  --prep_def_merge_tr_red                 false
% 31.87/4.49  --prep_def_merge_tr_cl                  false
% 31.87/4.49  --smt_preprocessing                     true
% 31.87/4.49  --smt_ac_axioms                         fast
% 31.87/4.49  --preprocessed_out                      false
% 31.87/4.49  --preprocessed_stats                    false
% 31.87/4.49  
% 31.87/4.49  ------ Abstraction refinement Options
% 31.87/4.49  
% 31.87/4.49  --abstr_ref                             []
% 31.87/4.49  --abstr_ref_prep                        false
% 31.87/4.49  --abstr_ref_until_sat                   false
% 31.87/4.49  --abstr_ref_sig_restrict                funpre
% 31.87/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.87/4.49  --abstr_ref_under                       []
% 31.87/4.49  
% 31.87/4.49  ------ SAT Options
% 31.87/4.49  
% 31.87/4.49  --sat_mode                              false
% 31.87/4.49  --sat_fm_restart_options                ""
% 31.87/4.49  --sat_gr_def                            false
% 31.87/4.49  --sat_epr_types                         true
% 31.87/4.49  --sat_non_cyclic_types                  false
% 31.87/4.49  --sat_finite_models                     false
% 31.87/4.49  --sat_fm_lemmas                         false
% 31.87/4.49  --sat_fm_prep                           false
% 31.87/4.49  --sat_fm_uc_incr                        true
% 31.87/4.49  --sat_out_model                         small
% 31.87/4.49  --sat_out_clauses                       false
% 31.87/4.49  
% 31.87/4.49  ------ QBF Options
% 31.87/4.49  
% 31.87/4.49  --qbf_mode                              false
% 31.87/4.49  --qbf_elim_univ                         false
% 31.87/4.49  --qbf_dom_inst                          none
% 31.87/4.49  --qbf_dom_pre_inst                      false
% 31.87/4.49  --qbf_sk_in                             false
% 31.87/4.49  --qbf_pred_elim                         true
% 31.87/4.49  --qbf_split                             512
% 31.87/4.49  
% 31.87/4.49  ------ BMC1 Options
% 31.87/4.49  
% 31.87/4.49  --bmc1_incremental                      false
% 31.87/4.49  --bmc1_axioms                           reachable_all
% 31.87/4.49  --bmc1_min_bound                        0
% 31.87/4.49  --bmc1_max_bound                        -1
% 31.87/4.49  --bmc1_max_bound_default                -1
% 31.87/4.49  --bmc1_symbol_reachability              true
% 31.87/4.49  --bmc1_property_lemmas                  false
% 31.87/4.49  --bmc1_k_induction                      false
% 31.87/4.49  --bmc1_non_equiv_states                 false
% 31.87/4.49  --bmc1_deadlock                         false
% 31.87/4.49  --bmc1_ucm                              false
% 31.87/4.49  --bmc1_add_unsat_core                   none
% 31.87/4.49  --bmc1_unsat_core_children              false
% 31.87/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.87/4.49  --bmc1_out_stat                         full
% 31.87/4.49  --bmc1_ground_init                      false
% 31.87/4.49  --bmc1_pre_inst_next_state              false
% 31.87/4.49  --bmc1_pre_inst_state                   false
% 31.87/4.49  --bmc1_pre_inst_reach_state             false
% 31.87/4.49  --bmc1_out_unsat_core                   false
% 31.87/4.49  --bmc1_aig_witness_out                  false
% 31.87/4.49  --bmc1_verbose                          false
% 31.87/4.49  --bmc1_dump_clauses_tptp                false
% 31.87/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.87/4.49  --bmc1_dump_file                        -
% 31.87/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.87/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.87/4.49  --bmc1_ucm_extend_mode                  1
% 31.87/4.49  --bmc1_ucm_init_mode                    2
% 31.87/4.49  --bmc1_ucm_cone_mode                    none
% 31.87/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.87/4.49  --bmc1_ucm_relax_model                  4
% 31.87/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.87/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.87/4.49  --bmc1_ucm_layered_model                none
% 31.87/4.49  --bmc1_ucm_max_lemma_size               10
% 31.87/4.49  
% 31.87/4.49  ------ AIG Options
% 31.87/4.49  
% 31.87/4.49  --aig_mode                              false
% 31.87/4.49  
% 31.87/4.49  ------ Instantiation Options
% 31.87/4.49  
% 31.87/4.49  --instantiation_flag                    true
% 31.87/4.49  --inst_sos_flag                         true
% 31.87/4.49  --inst_sos_phase                        true
% 31.87/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.87/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.87/4.49  --inst_lit_sel_side                     none
% 31.87/4.49  --inst_solver_per_active                1400
% 31.87/4.49  --inst_solver_calls_frac                1.
% 31.87/4.49  --inst_passive_queue_type               priority_queues
% 31.87/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.87/4.49  --inst_passive_queues_freq              [25;2]
% 31.87/4.49  --inst_dismatching                      true
% 31.87/4.49  --inst_eager_unprocessed_to_passive     true
% 31.87/4.49  --inst_prop_sim_given                   true
% 31.87/4.49  --inst_prop_sim_new                     false
% 31.87/4.49  --inst_subs_new                         false
% 31.87/4.49  --inst_eq_res_simp                      false
% 31.87/4.49  --inst_subs_given                       false
% 31.87/4.49  --inst_orphan_elimination               true
% 31.87/4.49  --inst_learning_loop_flag               true
% 31.87/4.49  --inst_learning_start                   3000
% 31.87/4.49  --inst_learning_factor                  2
% 31.87/4.49  --inst_start_prop_sim_after_learn       3
% 31.87/4.49  --inst_sel_renew                        solver
% 31.87/4.49  --inst_lit_activity_flag                true
% 31.87/4.49  --inst_restr_to_given                   false
% 31.87/4.49  --inst_activity_threshold               500
% 31.87/4.49  --inst_out_proof                        true
% 31.87/4.49  
% 31.87/4.49  ------ Resolution Options
% 31.87/4.49  
% 31.87/4.49  --resolution_flag                       false
% 31.87/4.49  --res_lit_sel                           adaptive
% 31.87/4.49  --res_lit_sel_side                      none
% 31.87/4.49  --res_ordering                          kbo
% 31.87/4.49  --res_to_prop_solver                    active
% 31.87/4.49  --res_prop_simpl_new                    false
% 31.87/4.49  --res_prop_simpl_given                  true
% 31.87/4.49  --res_passive_queue_type                priority_queues
% 31.87/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.87/4.49  --res_passive_queues_freq               [15;5]
% 31.87/4.49  --res_forward_subs                      full
% 31.87/4.49  --res_backward_subs                     full
% 31.87/4.49  --res_forward_subs_resolution           true
% 31.87/4.49  --res_backward_subs_resolution          true
% 31.87/4.49  --res_orphan_elimination                true
% 31.87/4.49  --res_time_limit                        2.
% 31.87/4.49  --res_out_proof                         true
% 31.87/4.49  
% 31.87/4.49  ------ Superposition Options
% 31.87/4.49  
% 31.87/4.49  --superposition_flag                    true
% 31.87/4.49  --sup_passive_queue_type                priority_queues
% 31.87/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.87/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.87/4.49  --demod_completeness_check              fast
% 31.87/4.49  --demod_use_ground                      true
% 31.87/4.49  --sup_to_prop_solver                    passive
% 31.87/4.49  --sup_prop_simpl_new                    true
% 31.87/4.49  --sup_prop_simpl_given                  true
% 31.87/4.49  --sup_fun_splitting                     true
% 31.87/4.49  --sup_smt_interval                      50000
% 31.87/4.49  
% 31.87/4.49  ------ Superposition Simplification Setup
% 31.87/4.49  
% 31.87/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.87/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.87/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.87/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.87/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.87/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.87/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.87/4.49  --sup_immed_triv                        [TrivRules]
% 31.87/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.87/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.87/4.49  --sup_immed_bw_main                     []
% 31.87/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.87/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.87/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.87/4.49  --sup_input_bw                          []
% 31.87/4.49  
% 31.87/4.49  ------ Combination Options
% 31.87/4.49  
% 31.87/4.49  --comb_res_mult                         3
% 31.87/4.49  --comb_sup_mult                         2
% 31.87/4.49  --comb_inst_mult                        10
% 31.87/4.49  
% 31.87/4.49  ------ Debug Options
% 31.87/4.49  
% 31.87/4.49  --dbg_backtrace                         false
% 31.87/4.49  --dbg_dump_prop_clauses                 false
% 31.87/4.49  --dbg_dump_prop_clauses_file            -
% 31.87/4.49  --dbg_out_stat                          false
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  % SZS status Theorem for theBenchmark.p
% 31.87/4.49  
% 31.87/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.87/4.49  
% 31.87/4.49  fof(f10,axiom,(
% 31.87/4.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f51,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f10])).
% 31.87/4.49  
% 31.87/4.49  fof(f6,axiom,(
% 31.87/4.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f47,plain,(
% 31.87/4.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f6])).
% 31.87/4.49  
% 31.87/4.49  fof(f5,axiom,(
% 31.87/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f23,plain,(
% 31.87/4.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.87/4.49    inference(ennf_transformation,[],[f5])).
% 31.87/4.49  
% 31.87/4.49  fof(f46,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f23])).
% 31.87/4.49  
% 31.87/4.49  fof(f9,axiom,(
% 31.87/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f50,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.87/4.49    inference(cnf_transformation,[],[f9])).
% 31.87/4.49  
% 31.87/4.49  fof(f68,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 31.87/4.49    inference(definition_unfolding,[],[f46,f50])).
% 31.87/4.49  
% 31.87/4.49  fof(f13,axiom,(
% 31.87/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f54,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.87/4.49    inference(cnf_transformation,[],[f13])).
% 31.87/4.49  
% 31.87/4.49  fof(f69,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.87/4.49    inference(definition_unfolding,[],[f54,f50])).
% 31.87/4.49  
% 31.87/4.49  fof(f19,conjecture,(
% 31.87/4.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f20,negated_conjecture,(
% 31.87/4.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 31.87/4.49    inference(negated_conjecture,[],[f19])).
% 31.87/4.49  
% 31.87/4.49  fof(f35,plain,(
% 31.87/4.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 31.87/4.49    inference(ennf_transformation,[],[f20])).
% 31.87/4.49  
% 31.87/4.49  fof(f36,plain,(
% 31.87/4.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.87/4.49    inference(flattening,[],[f35])).
% 31.87/4.49  
% 31.87/4.49  fof(f37,plain,(
% 31.87/4.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.87/4.49    inference(nnf_transformation,[],[f36])).
% 31.87/4.49  
% 31.87/4.49  fof(f38,plain,(
% 31.87/4.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.87/4.49    inference(flattening,[],[f37])).
% 31.87/4.49  
% 31.87/4.49  fof(f40,plain,(
% 31.87/4.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.87/4.49    introduced(choice_axiom,[])).
% 31.87/4.49  
% 31.87/4.49  fof(f39,plain,(
% 31.87/4.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 31.87/4.49    introduced(choice_axiom,[])).
% 31.87/4.49  
% 31.87/4.49  fof(f41,plain,(
% 31.87/4.49    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 31.87/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 31.87/4.49  
% 31.87/4.49  fof(f63,plain,(
% 31.87/4.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.87/4.49    inference(cnf_transformation,[],[f41])).
% 31.87/4.49  
% 31.87/4.49  fof(f12,axiom,(
% 31.87/4.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f26,plain,(
% 31.87/4.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.87/4.49    inference(ennf_transformation,[],[f12])).
% 31.87/4.49  
% 31.87/4.49  fof(f53,plain,(
% 31.87/4.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.87/4.49    inference(cnf_transformation,[],[f26])).
% 31.87/4.49  
% 31.87/4.49  fof(f18,axiom,(
% 31.87/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f34,plain,(
% 31.87/4.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.87/4.49    inference(ennf_transformation,[],[f18])).
% 31.87/4.49  
% 31.87/4.49  fof(f60,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f34])).
% 31.87/4.49  
% 31.87/4.49  fof(f62,plain,(
% 31.87/4.49    l1_pre_topc(sK0)),
% 31.87/4.49    inference(cnf_transformation,[],[f41])).
% 31.87/4.49  
% 31.87/4.49  fof(f64,plain,(
% 31.87/4.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 31.87/4.49    inference(cnf_transformation,[],[f41])).
% 31.87/4.49  
% 31.87/4.49  fof(f14,axiom,(
% 31.87/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f27,plain,(
% 31.87/4.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.87/4.49    inference(ennf_transformation,[],[f14])).
% 31.87/4.49  
% 31.87/4.49  fof(f28,plain,(
% 31.87/4.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.87/4.49    inference(flattening,[],[f27])).
% 31.87/4.49  
% 31.87/4.49  fof(f55,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f28])).
% 31.87/4.49  
% 31.87/4.49  fof(f17,axiom,(
% 31.87/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f32,plain,(
% 31.87/4.49    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.87/4.49    inference(ennf_transformation,[],[f17])).
% 31.87/4.49  
% 31.87/4.49  fof(f33,plain,(
% 31.87/4.49    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.87/4.49    inference(flattening,[],[f32])).
% 31.87/4.49  
% 31.87/4.49  fof(f59,plain,(
% 31.87/4.49    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f33])).
% 31.87/4.49  
% 31.87/4.49  fof(f65,plain,(
% 31.87/4.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 31.87/4.49    inference(cnf_transformation,[],[f41])).
% 31.87/4.49  
% 31.87/4.49  fof(f56,plain,(
% 31.87/4.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f28])).
% 31.87/4.49  
% 31.87/4.49  fof(f61,plain,(
% 31.87/4.49    v2_pre_topc(sK0)),
% 31.87/4.49    inference(cnf_transformation,[],[f41])).
% 31.87/4.49  
% 31.87/4.49  fof(f2,axiom,(
% 31.87/4.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f43,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.87/4.49    inference(cnf_transformation,[],[f2])).
% 31.87/4.49  
% 31.87/4.49  fof(f66,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 31.87/4.49    inference(definition_unfolding,[],[f43,f50])).
% 31.87/4.49  
% 31.87/4.49  fof(f3,axiom,(
% 31.87/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f22,plain,(
% 31.87/4.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 31.87/4.49    inference(ennf_transformation,[],[f3])).
% 31.87/4.49  
% 31.87/4.49  fof(f44,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f22])).
% 31.87/4.49  
% 31.87/4.49  fof(f4,axiom,(
% 31.87/4.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f45,plain,(
% 31.87/4.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.87/4.49    inference(cnf_transformation,[],[f4])).
% 31.87/4.49  
% 31.87/4.49  fof(f8,axiom,(
% 31.87/4.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f49,plain,(
% 31.87/4.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.87/4.49    inference(cnf_transformation,[],[f8])).
% 31.87/4.49  
% 31.87/4.49  fof(f1,axiom,(
% 31.87/4.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f21,plain,(
% 31.87/4.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 31.87/4.49    inference(rectify,[],[f1])).
% 31.87/4.49  
% 31.87/4.49  fof(f42,plain,(
% 31.87/4.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 31.87/4.49    inference(cnf_transformation,[],[f21])).
% 31.87/4.49  
% 31.87/4.49  fof(f67,plain,(
% 31.87/4.49    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 31.87/4.49    inference(definition_unfolding,[],[f42,f50])).
% 31.87/4.49  
% 31.87/4.49  fof(f7,axiom,(
% 31.87/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f48,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 31.87/4.49    inference(cnf_transformation,[],[f7])).
% 31.87/4.49  
% 31.87/4.49  fof(f15,axiom,(
% 31.87/4.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f29,plain,(
% 31.87/4.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.87/4.49    inference(ennf_transformation,[],[f15])).
% 31.87/4.49  
% 31.87/4.49  fof(f30,plain,(
% 31.87/4.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.87/4.49    inference(flattening,[],[f29])).
% 31.87/4.49  
% 31.87/4.49  fof(f57,plain,(
% 31.87/4.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f30])).
% 31.87/4.49  
% 31.87/4.49  fof(f11,axiom,(
% 31.87/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f24,plain,(
% 31.87/4.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.87/4.49    inference(ennf_transformation,[],[f11])).
% 31.87/4.49  
% 31.87/4.49  fof(f25,plain,(
% 31.87/4.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.87/4.49    inference(flattening,[],[f24])).
% 31.87/4.49  
% 31.87/4.49  fof(f52,plain,(
% 31.87/4.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.87/4.49    inference(cnf_transformation,[],[f25])).
% 31.87/4.49  
% 31.87/4.49  fof(f16,axiom,(
% 31.87/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 31.87/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f31,plain,(
% 31.87/4.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.87/4.49    inference(ennf_transformation,[],[f16])).
% 31.87/4.49  
% 31.87/4.49  fof(f58,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f31])).
% 31.87/4.49  
% 31.87/4.49  cnf(c_8,plain,
% 31.87/4.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f51]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5,plain,
% 31.87/4.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f47]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1111,plain,
% 31.87/4.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4,plain,
% 31.87/4.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 31.87/4.49      inference(cnf_transformation,[],[f68]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1112,plain,
% 31.87/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 31.87/4.49      | r1_tarski(X0,X1) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_11,plain,
% 31.87/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 31.87/4.49      inference(cnf_transformation,[],[f69]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1115,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 31.87/4.49      | r1_tarski(X0,X1) != iProver_top ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_1112,c_11]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4719,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1111,c_1115]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_12046,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_8,c_4719]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_20,negated_conjecture,
% 31.87/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.87/4.49      inference(cnf_transformation,[],[f63]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1108,plain,
% 31.87/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_10,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.87/4.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 31.87/4.49      inference(cnf_transformation,[],[f53]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1109,plain,
% 31.87/4.49      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 31.87/4.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5842,plain,
% 31.87/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1108,c_1109]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_17,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | ~ l1_pre_topc(X1)
% 31.87/4.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f60]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_21,negated_conjecture,
% 31.87/4.49      ( l1_pre_topc(sK0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f62]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_325,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 31.87/4.49      | sK0 != X1 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_326,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_325]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1107,plain,
% 31.87/4.49      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 31.87/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1264,plain,
% 31.87/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1108,c_1107]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6458,plain,
% 31.87/4.49      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_5842,c_1264]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1996,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_11,c_11]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4799,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_8,c_1996]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4828,plain,
% 31.87/4.49      ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_4799,c_11]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6887,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)))) = k4_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_6458,c_4828]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6896,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)))) = k1_setfam_1(k2_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_6887,c_1996]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_12171,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_12046,c_6896]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_19,negated_conjecture,
% 31.87/4.49      ( v4_pre_topc(sK1,sK0)
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(cnf_transformation,[],[f64]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_139,plain,
% 31.87/4.49      ( v4_pre_topc(sK1,sK0)
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(prop_impl,[status(thm)],[c_19]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_13,plain,
% 31.87/4.49      ( ~ v4_pre_topc(X0,X1)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | ~ l1_pre_topc(X1)
% 31.87/4.49      | k2_pre_topc(X1,X0) = X0 ),
% 31.87/4.49      inference(cnf_transformation,[],[f55]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_376,plain,
% 31.87/4.49      ( ~ v4_pre_topc(X0,X1)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | k2_pre_topc(X1,X0) = X0
% 31.87/4.49      | sK0 != X1 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_377,plain,
% 31.87/4.49      ( ~ v4_pre_topc(X0,sK0)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | k2_pre_topc(sK0,X0) = X0 ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_376]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_472,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.87/4.49      | k2_pre_topc(sK0,X0) = X0
% 31.87/4.49      | sK1 != X0
% 31.87/4.49      | sK0 != sK0 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_139,c_377]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_473,plain,
% 31.87/4.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.87/4.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_472]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_475,plain,
% 31.87/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.87/4.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 31.87/4.49      inference(global_propositional_subsumption,
% 31.87/4.49                [status(thm)],
% 31.87/4.49                [c_473,c_20]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_629,plain,
% 31.87/4.49      ( k2_pre_topc(sK0,sK1) = sK1
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(prop_impl,[status(thm)],[c_475]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_630,plain,
% 31.87/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.87/4.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 31.87/4.49      inference(renaming,[status(thm)],[c_629]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6457,plain,
% 31.87/4.49      ( k2_pre_topc(sK0,sK1) = sK1
% 31.87/4.49      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_5842,c_630]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_7715,plain,
% 31.87/4.49      ( k2_pre_topc(sK0,sK1) = sK1
% 31.87/4.49      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_6457,c_1111]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_16,plain,
% 31.87/4.49      ( ~ v4_pre_topc(X0,X1)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | r1_tarski(k2_tops_1(X1,X0),X0)
% 31.87/4.49      | ~ l1_pre_topc(X1) ),
% 31.87/4.49      inference(cnf_transformation,[],[f59]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_337,plain,
% 31.87/4.49      ( ~ v4_pre_topc(X0,X1)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | r1_tarski(k2_tops_1(X1,X0),X0)
% 31.87/4.49      | sK0 != X1 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_338,plain,
% 31.87/4.49      ( ~ v4_pre_topc(X0,sK0)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | r1_tarski(k2_tops_1(sK0,X0),X0) ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_337]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_483,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | r1_tarski(k2_tops_1(sK0,X0),X0)
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.87/4.49      | sK1 != X0
% 31.87/4.49      | sK0 != sK0 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_139,c_338]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_484,plain,
% 31.87/4.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_483]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_486,plain,
% 31.87/4.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(global_propositional_subsumption,
% 31.87/4.49                [status(thm)],
% 31.87/4.49                [c_484,c_20]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_18,negated_conjecture,
% 31.87/4.49      ( ~ v4_pre_topc(sK1,sK0)
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(cnf_transformation,[],[f65]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_137,plain,
% 31.87/4.49      ( ~ v4_pre_topc(sK1,sK0)
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(prop_impl,[status(thm)],[c_18]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_12,plain,
% 31.87/4.49      ( v4_pre_topc(X0,X1)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | ~ l1_pre_topc(X1)
% 31.87/4.49      | ~ v2_pre_topc(X1)
% 31.87/4.49      | k2_pre_topc(X1,X0) != X0 ),
% 31.87/4.49      inference(cnf_transformation,[],[f56]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_22,negated_conjecture,
% 31.87/4.49      ( v2_pre_topc(sK0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f61]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_242,plain,
% 31.87/4.49      ( v4_pre_topc(X0,X1)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | ~ l1_pre_topc(X1)
% 31.87/4.49      | k2_pre_topc(X1,X0) != X0
% 31.87/4.49      | sK0 != X1 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_243,plain,
% 31.87/4.49      ( v4_pre_topc(X0,sK0)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | ~ l1_pre_topc(sK0)
% 31.87/4.49      | k2_pre_topc(sK0,X0) != X0 ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_242]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_247,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | v4_pre_topc(X0,sK0)
% 31.87/4.49      | k2_pre_topc(sK0,X0) != X0 ),
% 31.87/4.49      inference(global_propositional_subsumption,
% 31.87/4.49                [status(thm)],
% 31.87/4.49                [c_243,c_21]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_248,plain,
% 31.87/4.49      ( v4_pre_topc(X0,sK0)
% 31.87/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | k2_pre_topc(sK0,X0) != X0 ),
% 31.87/4.49      inference(renaming,[status(thm)],[c_247]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_497,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 31.87/4.49      | k2_pre_topc(sK0,X0) != X0
% 31.87/4.49      | sK1 != X0
% 31.87/4.49      | sK0 != sK0 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_137,c_248]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_498,plain,
% 31.87/4.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 31.87/4.49      | k2_pre_topc(sK0,sK1) != sK1 ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_497]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_500,plain,
% 31.87/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 31.87/4.49      | k2_pre_topc(sK0,sK1) != sK1 ),
% 31.87/4.49      inference(global_propositional_subsumption,
% 31.87/4.49                [status(thm)],
% 31.87/4.49                [c_498,c_20]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_627,plain,
% 31.87/4.49      ( k2_pre_topc(sK0,sK1) != sK1
% 31.87/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(prop_impl,[status(thm)],[c_500]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_628,plain,
% 31.87/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 31.87/4.49      | k2_pre_topc(sK0,sK1) != sK1 ),
% 31.87/4.49      inference(renaming,[status(thm)],[c_627]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_659,plain,
% 31.87/4.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) | k2_pre_topc(sK0,sK1) != sK1 ),
% 31.87/4.49      inference(bin_hyper_res,[status(thm)],[c_486,c_628]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_667,plain,
% 31.87/4.49      ( k2_pre_topc(sK0,sK1) != sK1
% 31.87/4.49      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_17696,plain,
% 31.87/4.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.87/4.49      inference(global_propositional_subsumption,
% 31.87/4.49                [status(thm)],
% 31.87/4.49                [c_7715,c_667]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_17700,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_17696,c_1115]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_2035,plain,
% 31.87/4.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_11,c_1111]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4720,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_2035,c_1115]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_13611,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_8,c_4720]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_14420,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_13611,c_4720]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_12075,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_4719,c_4799]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_12078,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 31.87/4.49      inference(light_normalisation,[status(thm)],[c_12075,c_11]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_14424,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_13611,c_12078]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_14438,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_14424,c_13611]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_14440,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_14420,c_13611,c_14438]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_18632,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_17700,c_14440]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_21531,plain,
% 31.87/4.49      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(light_normalisation,
% 31.87/4.49                [status(thm)],
% 31.87/4.49                [c_12171,c_12171,c_17700,c_18632]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_0,plain,
% 31.87/4.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.87/4.49      inference(cnf_transformation,[],[f66]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1114,plain,
% 31.87/4.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.87/4.49      inference(light_normalisation,[status(thm)],[c_0,c_11]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_12070,plain,
% 31.87/4.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_4719,c_1114]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_2,plain,
% 31.87/4.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 31.87/4.49      inference(cnf_transformation,[],[f44]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1113,plain,
% 31.87/4.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4712,plain,
% 31.87/4.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1111,c_1113]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_3,plain,
% 31.87/4.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.87/4.49      inference(cnf_transformation,[],[f45]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_8223,plain,
% 31.87/4.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_4712,c_3]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_8596,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_8223,c_11]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_7,plain,
% 31.87/4.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.87/4.49      inference(cnf_transformation,[],[f49]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1995,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_7,c_11]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_2471,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_8,c_1995]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_8637,plain,
% 31.87/4.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_8596,c_2471]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1,plain,
% 31.87/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 31.87/4.49      inference(cnf_transformation,[],[f67]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1997,plain,
% 31.87/4.49      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_3231,plain,
% 31.87/4.49      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1997,c_1114]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_9201,plain,
% 31.87/4.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_8637,c_3231]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_12080,plain,
% 31.87/4.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_12070,c_9201]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6,plain,
% 31.87/4.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 31.87/4.49      inference(cnf_transformation,[],[f48]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_105049,plain,
% 31.87/4.49      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_12080,c_6]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_105051,plain,
% 31.87/4.49      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 31.87/4.49      inference(light_normalisation,[status(thm)],[c_105049,c_3]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_106996,plain,
% 31.87/4.49      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_21531,c_105051]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_14,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | ~ l1_pre_topc(X1) ),
% 31.87/4.49      inference(cnf_transformation,[],[f57]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_364,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | sK0 != X1 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_365,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_364]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1105,plain,
% 31.87/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.87/4.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_9,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.87/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.87/4.49      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f52]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1110,plain,
% 31.87/4.49      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 31.87/4.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 31.87/4.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_7525,plain,
% 31.87/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 31.87/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1108,c_1110]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_7590,plain,
% 31.87/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 31.87/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1105,c_7525]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_7629,plain,
% 31.87/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1108,c_7590]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_15,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | ~ l1_pre_topc(X1)
% 31.87/4.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f58]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_352,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.87/4.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 31.87/4.49      | sK0 != X1 ),
% 31.87/4.49      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_353,plain,
% 31.87/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.87/4.49      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 31.87/4.49      inference(unflattening,[status(thm)],[c_352]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1106,plain,
% 31.87/4.49      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 31.87/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_1212,plain,
% 31.87/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_1108,c_1106]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_7631,plain,
% 31.87/4.49      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.87/4.49      inference(light_normalisation,[status(thm)],[c_7629,c_1212]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_109061,plain,
% 31.87/4.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_106996,c_7631]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6454,plain,
% 31.87/4.49      ( k2_pre_topc(sK0,sK1) != sK1
% 31.87/4.49      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 31.87/4.49      inference(demodulation,[status(thm)],[c_5842,c_628]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(contradiction,plain,
% 31.87/4.49      ( $false ),
% 31.87/4.49      inference(minisat,[status(thm)],[c_109061,c_21531,c_6454]) ).
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.87/4.49  
% 31.87/4.49  ------                               Statistics
% 31.87/4.49  
% 31.87/4.49  ------ General
% 31.87/4.49  
% 31.87/4.49  abstr_ref_over_cycles:                  0
% 31.87/4.49  abstr_ref_under_cycles:                 0
% 31.87/4.49  gc_basic_clause_elim:                   0
% 31.87/4.49  forced_gc_time:                         0
% 31.87/4.49  parsing_time:                           0.007
% 31.87/4.49  unif_index_cands_time:                  0.
% 31.87/4.49  unif_index_add_time:                    0.
% 31.87/4.49  orderings_time:                         0.
% 31.87/4.49  out_proof_time:                         0.019
% 31.87/4.49  total_time:                             3.998
% 31.87/4.49  num_of_symbols:                         51
% 31.87/4.49  num_of_terms:                           89658
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing
% 31.87/4.49  
% 31.87/4.49  num_of_splits:                          0
% 31.87/4.49  num_of_split_atoms:                     0
% 31.87/4.49  num_of_reused_defs:                     0
% 31.87/4.49  num_eq_ax_congr_red:                    21
% 31.87/4.49  num_of_sem_filtered_clauses:            1
% 31.87/4.49  num_of_subtypes:                        0
% 31.87/4.49  monotx_restored_types:                  0
% 31.87/4.49  sat_num_of_epr_types:                   0
% 31.87/4.49  sat_num_of_non_cyclic_types:            0
% 31.87/4.49  sat_guarded_non_collapsed_types:        0
% 31.87/4.49  num_pure_diseq_elim:                    0
% 31.87/4.49  simp_replaced_by:                       0
% 31.87/4.49  res_preprocessed:                       114
% 31.87/4.49  prep_upred:                             0
% 31.87/4.49  prep_unflattend:                        49
% 31.87/4.49  smt_new_axioms:                         0
% 31.87/4.49  pred_elim_cands:                        2
% 31.87/4.49  pred_elim:                              3
% 31.87/4.49  pred_elim_cl:                           3
% 31.87/4.49  pred_elim_cycles:                       7
% 31.87/4.49  merged_defs:                            8
% 31.87/4.49  merged_defs_ncl:                        0
% 31.87/4.49  bin_hyper_res:                          9
% 31.87/4.49  prep_cycles:                            4
% 31.87/4.49  pred_elim_time:                         0.005
% 31.87/4.49  splitting_time:                         0.
% 31.87/4.49  sem_filter_time:                        0.
% 31.87/4.49  monotx_time:                            0.
% 31.87/4.49  subtype_inf_time:                       0.
% 31.87/4.49  
% 31.87/4.49  ------ Problem properties
% 31.87/4.49  
% 31.87/4.49  clauses:                                20
% 31.87/4.49  conjectures:                            1
% 31.87/4.49  epr:                                    0
% 31.87/4.49  horn:                                   19
% 31.87/4.49  ground:                                 4
% 31.87/4.49  unary:                                  9
% 31.87/4.49  binary:                                 9
% 31.87/4.49  lits:                                   33
% 31.87/4.49  lits_eq:                                19
% 31.87/4.49  fd_pure:                                0
% 31.87/4.49  fd_pseudo:                              0
% 31.87/4.49  fd_cond:                                0
% 31.87/4.49  fd_pseudo_cond:                         0
% 31.87/4.49  ac_symbols:                             0
% 31.87/4.49  
% 31.87/4.49  ------ Propositional Solver
% 31.87/4.49  
% 31.87/4.49  prop_solver_calls:                      51
% 31.87/4.49  prop_fast_solver_calls:                 2537
% 31.87/4.49  smt_solver_calls:                       0
% 31.87/4.49  smt_fast_solver_calls:                  0
% 31.87/4.49  prop_num_of_clauses:                    40664
% 31.87/4.49  prop_preprocess_simplified:             89221
% 31.87/4.49  prop_fo_subsumed:                       21
% 31.87/4.49  prop_solver_time:                       0.
% 31.87/4.49  smt_solver_time:                        0.
% 31.87/4.49  smt_fast_solver_time:                   0.
% 31.87/4.49  prop_fast_solver_time:                  0.
% 31.87/4.49  prop_unsat_core_time:                   0.005
% 31.87/4.49  
% 31.87/4.49  ------ QBF
% 31.87/4.49  
% 31.87/4.49  qbf_q_res:                              0
% 31.87/4.49  qbf_num_tautologies:                    0
% 31.87/4.49  qbf_prep_cycles:                        0
% 31.87/4.49  
% 31.87/4.49  ------ BMC1
% 31.87/4.49  
% 31.87/4.49  bmc1_current_bound:                     -1
% 31.87/4.49  bmc1_last_solved_bound:                 -1
% 31.87/4.49  bmc1_unsat_core_size:                   -1
% 31.87/4.49  bmc1_unsat_core_parents_size:           -1
% 31.87/4.49  bmc1_merge_next_fun:                    0
% 31.87/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.87/4.49  
% 31.87/4.49  ------ Instantiation
% 31.87/4.49  
% 31.87/4.49  inst_num_of_clauses:                    14437
% 31.87/4.49  inst_num_in_passive:                    6216
% 31.87/4.49  inst_num_in_active:                     5796
% 31.87/4.49  inst_num_in_unprocessed:                5173
% 31.87/4.49  inst_num_of_loops:                      6569
% 31.87/4.49  inst_num_of_learning_restarts:          1
% 31.87/4.49  inst_num_moves_active_passive:          763
% 31.87/4.49  inst_lit_activity:                      0
% 31.87/4.49  inst_lit_activity_moves:                4
% 31.87/4.49  inst_num_tautologies:                   0
% 31.87/4.49  inst_num_prop_implied:                  0
% 31.87/4.49  inst_num_existing_simplified:           0
% 31.87/4.49  inst_num_eq_res_simplified:             0
% 31.87/4.49  inst_num_child_elim:                    0
% 31.87/4.49  inst_num_of_dismatching_blockings:      7494
% 31.87/4.49  inst_num_of_non_proper_insts:           14886
% 31.87/4.49  inst_num_of_duplicates:                 0
% 31.87/4.49  inst_inst_num_from_inst_to_res:         0
% 31.87/4.49  inst_dismatching_checking_time:         0.
% 31.87/4.49  
% 31.87/4.49  ------ Resolution
% 31.87/4.49  
% 31.87/4.49  res_num_of_clauses:                     35
% 31.87/4.49  res_num_in_passive:                     35
% 31.87/4.49  res_num_in_active:                      0
% 31.87/4.49  res_num_of_loops:                       118
% 31.87/4.49  res_forward_subset_subsumed:            4365
% 31.87/4.49  res_backward_subset_subsumed:           6
% 31.87/4.49  res_forward_subsumed:                   0
% 31.87/4.49  res_backward_subsumed:                  0
% 31.87/4.49  res_forward_subsumption_resolution:     0
% 31.87/4.49  res_backward_subsumption_resolution:    0
% 31.87/4.49  res_clause_to_clause_subsumption:       18638
% 31.87/4.49  res_orphan_elimination:                 0
% 31.87/4.49  res_tautology_del:                      1951
% 31.87/4.49  res_num_eq_res_simplified:              0
% 31.87/4.49  res_num_sel_changes:                    0
% 31.87/4.49  res_moves_from_active_to_pass:          0
% 31.87/4.49  
% 31.87/4.49  ------ Superposition
% 31.87/4.49  
% 31.87/4.49  sup_time_total:                         0.
% 31.87/4.49  sup_time_generating:                    0.
% 31.87/4.49  sup_time_sim_full:                      0.
% 31.87/4.49  sup_time_sim_immed:                     0.
% 31.87/4.49  
% 31.87/4.49  sup_num_of_clauses:                     1649
% 31.87/4.49  sup_num_in_active:                      1266
% 31.87/4.49  sup_num_in_passive:                     383
% 31.87/4.49  sup_num_of_loops:                       1312
% 31.87/4.49  sup_fw_superposition:                   2236
% 31.87/4.49  sup_bw_superposition:                   2512
% 31.87/4.49  sup_immediate_simplified:               2286
% 31.87/4.49  sup_given_eliminated:                   0
% 31.87/4.49  comparisons_done:                       0
% 31.87/4.49  comparisons_avoided:                    15
% 31.87/4.49  
% 31.87/4.49  ------ Simplifications
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  sim_fw_subset_subsumed:                 1
% 31.87/4.49  sim_bw_subset_subsumed:                 1
% 31.87/4.49  sim_fw_subsumed:                        745
% 31.87/4.49  sim_bw_subsumed:                        7
% 31.87/4.49  sim_fw_subsumption_res:                 0
% 31.87/4.49  sim_bw_subsumption_res:                 0
% 31.87/4.49  sim_tautology_del:                      1
% 31.87/4.49  sim_eq_tautology_del:                   517
% 31.87/4.49  sim_eq_res_simp:                        1
% 31.87/4.49  sim_fw_demodulated:                     830
% 31.87/4.49  sim_bw_demodulated:                     81
% 31.87/4.49  sim_light_normalised:                   1214
% 31.87/4.49  sim_joinable_taut:                      0
% 31.87/4.49  sim_joinable_simp:                      0
% 31.87/4.49  sim_ac_normalised:                      0
% 31.87/4.49  sim_smt_subsumption:                    0
% 31.87/4.49  
%------------------------------------------------------------------------------

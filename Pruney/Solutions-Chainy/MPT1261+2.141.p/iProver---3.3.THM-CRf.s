%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:44 EST 2020

% Result     : Theorem 31.70s
% Output     : CNFRefutation 31.70s
% Verified   : 
% Statistics : Number of formulae       :  223 (4679 expanded)
%              Number of clauses        :  158 (2011 expanded)
%              Number of leaves         :   22 (1058 expanded)
%              Depth                    :   29
%              Number of atoms          :  486 (9339 expanded)
%              Number of equality atoms :  295 (4430 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f36])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f66,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f50,f50])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_775,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_774,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_781,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5195,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_781])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6004,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5195,c_25])).

cnf(c_6005,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6004])).

cnf(c_6010,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_775,c_6005])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3462,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_783])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_144,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_143])).

cnf(c_189,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_144])).

cnf(c_768,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_14088,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_3462,c_768])).

cnf(c_14125,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6010,c_14088])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_785,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_186,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_144])).

cnf(c_771,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_4857,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_785,c_771])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_187,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_144])).

cnf(c_770,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_4506,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_785,c_770])).

cnf(c_6387,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4857,c_4506])).

cnf(c_8968,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6387,c_4857])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1322,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_9597,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_8968,c_1322])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_786,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2282,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_785,c_786])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2513,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2282,c_3])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1314,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_2712,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2513,c_1314])).

cnf(c_2714,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2712,c_2513])).

cnf(c_2937,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2714,c_1322])).

cnf(c_2941,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2937,c_2714])).

cnf(c_2943,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2941,c_6])).

cnf(c_9613,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9597,c_2943])).

cnf(c_14878,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14125,c_9613])).

cnf(c_15224,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14878,c_4857])).

cnf(c_1321,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_785])).

cnf(c_2728,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2513,c_1321])).

cnf(c_4862,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2728,c_771])).

cnf(c_4864,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4862,c_6])).

cnf(c_15318,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_15224,c_4864])).

cnf(c_14087,plain,
    ( k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_785,c_768])).

cnf(c_44572,plain,
    ( k7_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_14087])).

cnf(c_79586,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),X0) = k7_subset_1(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_15318,c_44572])).

cnf(c_14091,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_2728,c_768])).

cnf(c_14096,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14091,c_2513])).

cnf(c_79675,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_79586,c_6,c_2714,c_9613,c_14096])).

cnf(c_2284,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1321,c_786])).

cnf(c_80334,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k1_xboole_0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_79675,c_2284])).

cnf(c_81098,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_80334,c_6])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_84393,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),X0) = k4_xboole_0(X0,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_81098,c_5])).

cnf(c_14090,plain,
    ( k7_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1321,c_768])).

cnf(c_50284,plain,
    ( k7_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_14090])).

cnf(c_1323,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_5560,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1323,c_2282])).

cnf(c_5569,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_5560])).

cnf(c_50832,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k7_subset_1(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_50284,c_5569])).

cnf(c_51462,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_50832,c_5,c_14087])).

cnf(c_59284,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_51462])).

cnf(c_59850,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_59284])).

cnf(c_80514,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_79675,c_59850])).

cnf(c_80518,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_80514,c_6])).

cnf(c_97578,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)) ),
    inference(superposition,[status(thm)],[c_80518,c_59850])).

cnf(c_97813,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_97578,c_6,c_2284,c_9613])).

cnf(c_773,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_784,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_777,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3584,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_777])).

cnf(c_12442,plain,
    ( k4_subset_1(u1_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1),k2_tops_1(X0,k4_xboole_0(u1_struct_0(X0),X1))) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_3584])).

cnf(c_37897,plain,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X0)) ),
    inference(superposition,[status(thm)],[c_773,c_12442])).

cnf(c_110520,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))))) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0)))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_97813,c_37897])).

cnf(c_110578,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))))) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X0))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_110520,c_37897])).

cnf(c_112199,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X0))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_84393,c_110578])).

cnf(c_942,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_963,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1122,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_259,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1168,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_1433,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_188,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_144])).

cnf(c_370,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_371,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_443,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_188,c_371])).

cnf(c_1117,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1520,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_260,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1434,plain,
    ( X0 != X1
    | k2_pre_topc(sK0,sK1) != X1
    | k2_pre_topc(sK0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_2682,plain,
    ( X0 != k2_pre_topc(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = X0
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_4827,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k2_pre_topc(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2682])).

cnf(c_2919,plain,
    ( X0 != X1
    | X0 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_6095,plain,
    ( X0 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | X0 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2919])).

cnf(c_9175,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6095])).

cnf(c_9176,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_9750,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9613,c_5])).

cnf(c_9753,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9750,c_3])).

cnf(c_14877,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_14125,c_9753])).

cnf(c_6987,plain,
    ( X0 != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,sK1) = X0
    | k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_25892,plain,
    ( k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6987])).

cnf(c_1153,plain,
    ( k2_pre_topc(sK0,sK1) != X0
    | k2_pre_topc(sK0,sK1) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_40119,plain,
    ( k2_pre_topc(sK0,sK1) != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,sK1) = sK1
    | sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1566,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_2707,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_114434,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != sK1
    | sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_114546,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_112199,c_22,c_21,c_942,c_963,c_1044,c_1122,c_1168,c_1433,c_1520,c_4827,c_9175,c_9176,c_14877,c_25892,c_40119,c_114434])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_778,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1973,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_778])).

cnf(c_1052,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2299,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1973,c_22,c_21,c_1052])).

cnf(c_114551,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_114546,c_2299])).

cnf(c_4858,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_3462,c_771])).

cnf(c_4507,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3462,c_770])).

cnf(c_5187,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4858,c_4507])).

cnf(c_6395,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_4857,c_5187])).

cnf(c_12445,plain,
    ( k4_subset_1(u1_struct_0(X0),k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))),k2_tops_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))))) = k2_pre_topc(X0,k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_3584])).

cnf(c_41356,plain,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k2_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))))) = k2_pre_topc(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))) ),
    inference(superposition,[status(thm)],[c_773,c_12445])).

cnf(c_38750,plain,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k2_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))))) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) ),
    inference(superposition,[status(thm)],[c_1,c_37897])).

cnf(c_41691,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))) ),
    inference(superposition,[status(thm)],[c_41356,c_38750])).

cnf(c_13,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_782,plain,
    ( k2_pre_topc(X0,X1) != X1
    | v4_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_42113,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) != k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_41691,c_782])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_43727,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) != k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42113,c_24,c_25])).

cnf(c_43740,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_43727])).

cnf(c_6436,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_6395,c_1322])).

cnf(c_6441,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6436,c_2943])).

cnf(c_43811,plain,
    ( k2_pre_topc(sK0,sK1) != k4_xboole_0(sK1,k1_xboole_0)
    | v4_pre_topc(k4_xboole_0(sK1,k1_xboole_0),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_43740,c_6441])).

cnf(c_43812,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43811,c_6])).

cnf(c_26,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_63300,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_43812,c_26])).

cnf(c_63301,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_63300])).

cnf(c_19,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_114551,c_114546,c_63301,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:10:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 31.70/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.70/4.50  
% 31.70/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.70/4.50  
% 31.70/4.50  ------  iProver source info
% 31.70/4.50  
% 31.70/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.70/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.70/4.50  git: non_committed_changes: false
% 31.70/4.50  git: last_make_outside_of_git: false
% 31.70/4.50  
% 31.70/4.50  ------ 
% 31.70/4.50  ------ Parsing...
% 31.70/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.70/4.50  
% 31.70/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 31.70/4.50  
% 31.70/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.70/4.50  
% 31.70/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.70/4.50  ------ Proving...
% 31.70/4.50  ------ Problem Properties 
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  clauses                                 24
% 31.70/4.50  conjectures                             5
% 31.70/4.50  EPR                                     2
% 31.70/4.50  Horn                                    23
% 31.70/4.50  unary                                   9
% 31.70/4.50  binary                                  8
% 31.70/4.50  lits                                    50
% 31.70/4.50  lits eq                                 16
% 31.70/4.50  fd_pure                                 0
% 31.70/4.50  fd_pseudo                               0
% 31.70/4.50  fd_cond                                 0
% 31.70/4.50  fd_pseudo_cond                          0
% 31.70/4.50  AC symbols                              0
% 31.70/4.50  
% 31.70/4.50  ------ Input Options Time Limit: Unbounded
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  ------ 
% 31.70/4.50  Current options:
% 31.70/4.50  ------ 
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  ------ Proving...
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  % SZS status Theorem for theBenchmark.p
% 31.70/4.50  
% 31.70/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.70/4.50  
% 31.70/4.50  fof(f19,conjecture,(
% 31.70/4.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f20,negated_conjecture,(
% 31.70/4.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 31.70/4.50    inference(negated_conjecture,[],[f19])).
% 31.70/4.50  
% 31.70/4.50  fof(f35,plain,(
% 31.70/4.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 31.70/4.50    inference(ennf_transformation,[],[f20])).
% 31.70/4.50  
% 31.70/4.50  fof(f36,plain,(
% 31.70/4.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.70/4.50    inference(flattening,[],[f35])).
% 31.70/4.50  
% 31.70/4.50  fof(f38,plain,(
% 31.70/4.50    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.70/4.50    inference(nnf_transformation,[],[f36])).
% 31.70/4.50  
% 31.70/4.50  fof(f39,plain,(
% 31.70/4.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.70/4.50    inference(flattening,[],[f38])).
% 31.70/4.50  
% 31.70/4.50  fof(f41,plain,(
% 31.70/4.50    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.70/4.50    introduced(choice_axiom,[])).
% 31.70/4.50  
% 31.70/4.50  fof(f40,plain,(
% 31.70/4.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 31.70/4.50    introduced(choice_axiom,[])).
% 31.70/4.50  
% 31.70/4.50  fof(f42,plain,(
% 31.70/4.50    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 31.70/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 31.70/4.50  
% 31.70/4.50  fof(f66,plain,(
% 31.70/4.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 31.70/4.50    inference(cnf_transformation,[],[f42])).
% 31.70/4.50  
% 31.70/4.50  fof(f65,plain,(
% 31.70/4.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.70/4.50    inference(cnf_transformation,[],[f42])).
% 31.70/4.50  
% 31.70/4.50  fof(f14,axiom,(
% 31.70/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f27,plain,(
% 31.70/4.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.50    inference(ennf_transformation,[],[f14])).
% 31.70/4.50  
% 31.70/4.50  fof(f28,plain,(
% 31.70/4.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.50    inference(flattening,[],[f27])).
% 31.70/4.50  
% 31.70/4.50  fof(f57,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f28])).
% 31.70/4.50  
% 31.70/4.50  fof(f64,plain,(
% 31.70/4.50    l1_pre_topc(sK0)),
% 31.70/4.50    inference(cnf_transformation,[],[f42])).
% 31.70/4.50  
% 31.70/4.50  fof(f13,axiom,(
% 31.70/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f37,plain,(
% 31.70/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.70/4.50    inference(nnf_transformation,[],[f13])).
% 31.70/4.50  
% 31.70/4.50  fof(f55,plain,(
% 31.70/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.70/4.50    inference(cnf_transformation,[],[f37])).
% 31.70/4.50  
% 31.70/4.50  fof(f12,axiom,(
% 31.70/4.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f26,plain,(
% 31.70/4.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.70/4.50    inference(ennf_transformation,[],[f12])).
% 31.70/4.50  
% 31.70/4.50  fof(f54,plain,(
% 31.70/4.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.70/4.50    inference(cnf_transformation,[],[f26])).
% 31.70/4.50  
% 31.70/4.50  fof(f56,plain,(
% 31.70/4.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f37])).
% 31.70/4.50  
% 31.70/4.50  fof(f5,axiom,(
% 31.70/4.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f47,plain,(
% 31.70/4.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f5])).
% 31.70/4.50  
% 31.70/4.50  fof(f9,axiom,(
% 31.70/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f22,plain,(
% 31.70/4.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.70/4.50    inference(ennf_transformation,[],[f9])).
% 31.70/4.50  
% 31.70/4.50  fof(f51,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.70/4.50    inference(cnf_transformation,[],[f22])).
% 31.70/4.50  
% 31.70/4.50  fof(f10,axiom,(
% 31.70/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f23,plain,(
% 31.70/4.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.70/4.50    inference(ennf_transformation,[],[f10])).
% 31.70/4.50  
% 31.70/4.50  fof(f52,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.70/4.50    inference(cnf_transformation,[],[f23])).
% 31.70/4.50  
% 31.70/4.50  fof(f1,axiom,(
% 31.70/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f43,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f1])).
% 31.70/4.50  
% 31.70/4.50  fof(f8,axiom,(
% 31.70/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f50,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.70/4.50    inference(cnf_transformation,[],[f8])).
% 31.70/4.50  
% 31.70/4.50  fof(f69,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 31.70/4.50    inference(definition_unfolding,[],[f43,f50,f50])).
% 31.70/4.50  
% 31.70/4.50  fof(f2,axiom,(
% 31.70/4.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f44,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.70/4.50    inference(cnf_transformation,[],[f2])).
% 31.70/4.50  
% 31.70/4.50  fof(f68,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 31.70/4.50    inference(definition_unfolding,[],[f44,f50])).
% 31.70/4.50  
% 31.70/4.50  fof(f3,axiom,(
% 31.70/4.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f21,plain,(
% 31.70/4.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 31.70/4.50    inference(ennf_transformation,[],[f3])).
% 31.70/4.50  
% 31.70/4.50  fof(f45,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f21])).
% 31.70/4.50  
% 31.70/4.50  fof(f4,axiom,(
% 31.70/4.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f46,plain,(
% 31.70/4.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.70/4.50    inference(cnf_transformation,[],[f4])).
% 31.70/4.50  
% 31.70/4.50  fof(f7,axiom,(
% 31.70/4.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f49,plain,(
% 31.70/4.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.70/4.50    inference(cnf_transformation,[],[f7])).
% 31.70/4.50  
% 31.70/4.50  fof(f6,axiom,(
% 31.70/4.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f48,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 31.70/4.50    inference(cnf_transformation,[],[f6])).
% 31.70/4.50  
% 31.70/4.50  fof(f18,axiom,(
% 31.70/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f34,plain,(
% 31.70/4.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.50    inference(ennf_transformation,[],[f18])).
% 31.70/4.50  
% 31.70/4.50  fof(f62,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f34])).
% 31.70/4.50  
% 31.70/4.50  fof(f15,axiom,(
% 31.70/4.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f29,plain,(
% 31.70/4.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.70/4.50    inference(ennf_transformation,[],[f15])).
% 31.70/4.50  
% 31.70/4.50  fof(f30,plain,(
% 31.70/4.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.70/4.50    inference(flattening,[],[f29])).
% 31.70/4.50  
% 31.70/4.50  fof(f59,plain,(
% 31.70/4.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f30])).
% 31.70/4.50  
% 31.70/4.50  fof(f11,axiom,(
% 31.70/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f24,plain,(
% 31.70/4.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.70/4.50    inference(ennf_transformation,[],[f11])).
% 31.70/4.50  
% 31.70/4.50  fof(f25,plain,(
% 31.70/4.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.70/4.50    inference(flattening,[],[f24])).
% 31.70/4.50  
% 31.70/4.50  fof(f53,plain,(
% 31.70/4.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.70/4.50    inference(cnf_transformation,[],[f25])).
% 31.70/4.50  
% 31.70/4.50  fof(f17,axiom,(
% 31.70/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 31.70/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.70/4.50  
% 31.70/4.50  fof(f33,plain,(
% 31.70/4.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.70/4.50    inference(ennf_transformation,[],[f17])).
% 31.70/4.50  
% 31.70/4.50  fof(f61,plain,(
% 31.70/4.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f33])).
% 31.70/4.50  
% 31.70/4.50  fof(f58,plain,(
% 31.70/4.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.70/4.50    inference(cnf_transformation,[],[f28])).
% 31.70/4.50  
% 31.70/4.50  fof(f63,plain,(
% 31.70/4.50    v2_pre_topc(sK0)),
% 31.70/4.50    inference(cnf_transformation,[],[f42])).
% 31.70/4.50  
% 31.70/4.50  fof(f67,plain,(
% 31.70/4.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 31.70/4.50    inference(cnf_transformation,[],[f42])).
% 31.70/4.50  
% 31.70/4.50  cnf(c_20,negated_conjecture,
% 31.70/4.50      ( v4_pre_topc(sK1,sK0)
% 31.70/4.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f66]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_775,plain,
% 31.70/4.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.70/4.50      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_21,negated_conjecture,
% 31.70/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.70/4.50      inference(cnf_transformation,[],[f65]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_774,plain,
% 31.70/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14,plain,
% 31.70/4.50      ( ~ v4_pre_topc(X0,X1)
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ l1_pre_topc(X1)
% 31.70/4.50      | k2_pre_topc(X1,X0) = X0 ),
% 31.70/4.50      inference(cnf_transformation,[],[f57]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_781,plain,
% 31.70/4.50      ( k2_pre_topc(X0,X1) = X1
% 31.70/4.50      | v4_pre_topc(X1,X0) != iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5195,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | v4_pre_topc(sK1,sK0) != iProver_top
% 31.70/4.50      | l1_pre_topc(sK0) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_774,c_781]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_22,negated_conjecture,
% 31.70/4.50      ( l1_pre_topc(sK0) ),
% 31.70/4.50      inference(cnf_transformation,[],[f64]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_25,plain,
% 31.70/4.50      ( l1_pre_topc(sK0) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6004,plain,
% 31.70/4.50      ( v4_pre_topc(sK1,sK0) != iProver_top
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_5195,c_25]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6005,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_6004]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6010,plain,
% 31.70/4.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_775,c_6005]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_12,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_783,plain,
% 31.70/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.70/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3462,plain,
% 31.70/4.50      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_774,c_783]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_10,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.70/4.50      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 31.70/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_11,plain,
% 31.70/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f56]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_143,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.70/4.50      inference(prop_impl,[status(thm)],[c_11]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_144,plain,
% 31.70/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_143]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_189,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 31.70/4.50      inference(bin_hyper_res,[status(thm)],[c_10,c_144]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_768,plain,
% 31.70/4.50      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14088,plain,
% 31.70/4.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3462,c_768]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14125,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6010,c_14088]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4,plain,
% 31.70/4.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 31.70/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_785,plain,
% 31.70/4.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_7,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.70/4.50      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 31.70/4.50      inference(cnf_transformation,[],[f51]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_186,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 31.70/4.50      inference(bin_hyper_res,[status(thm)],[c_7,c_144]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_771,plain,
% 31.70/4.50      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4857,plain,
% 31.70/4.50      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_785,c_771]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_8,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.70/4.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 31.70/4.50      inference(cnf_transformation,[],[f52]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_187,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 31.70/4.50      inference(bin_hyper_res,[status(thm)],[c_8,c_144]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_770,plain,
% 31.70/4.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 31.70/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4506,plain,
% 31.70/4.50      ( k3_subset_1(X0,k3_subset_1(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_785,c_770]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6387,plain,
% 31.70/4.50      ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_4857,c_4506]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_8968,plain,
% 31.70/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6387,c_4857]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1,plain,
% 31.70/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 31.70/4.50      inference(cnf_transformation,[],[f69]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_0,plain,
% 31.70/4.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f68]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1322,plain,
% 31.70/4.50      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9597,plain,
% 31.70/4.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_8968,c_1322]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 31.70/4.50      inference(cnf_transformation,[],[f45]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_786,plain,
% 31.70/4.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2282,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_785,c_786]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3,plain,
% 31.70/4.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.70/4.50      inference(cnf_transformation,[],[f46]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2513,plain,
% 31.70/4.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_2282,c_3]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6,plain,
% 31.70/4.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.70/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1314,plain,
% 31.70/4.50      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2712,plain,
% 31.70/4.50      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_2513,c_1314]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2714,plain,
% 31.70/4.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_2712,c_2513]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2937,plain,
% 31.70/4.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_2714,c_1322]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2941,plain,
% 31.70/4.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_2937,c_2714]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2943,plain,
% 31.70/4.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_2941,c_6]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9613,plain,
% 31.70/4.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_9597,c_2943]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14878,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_14125,c_9613]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_15224,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_14878,c_4857]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1321,plain,
% 31.70/4.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_785]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2728,plain,
% 31.70/4.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_2513,c_1321]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4862,plain,
% 31.70/4.50      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_2728,c_771]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4864,plain,
% 31.70/4.50      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_4862,c_6]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_15318,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_15224,c_4864]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14087,plain,
% 31.70/4.50      ( k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_785,c_768]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_44572,plain,
% 31.70/4.50      ( k7_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_14087]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_79586,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),X0) = k7_subset_1(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)),X0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_15318,c_44572]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14091,plain,
% 31.70/4.50      ( k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_2728,c_768]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14096,plain,
% 31.70/4.50      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_14091,c_2513]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_79675,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),X0) = k1_xboole_0 ),
% 31.70/4.50      inference(demodulation,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_79586,c_6,c_2714,c_9613,c_14096]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2284,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1321,c_786]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_80334,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k1_xboole_0),X0) = X0 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_79675,c_2284]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_81098,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),X0) = X0 ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_80334,c_6]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5,plain,
% 31.70/4.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_84393,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),X0) = k4_xboole_0(X0,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_81098,c_5]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14090,plain,
% 31.70/4.50      ( k7_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1321,c_768]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_50284,plain,
% 31.70/4.50      ( k7_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_14090]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1323,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5560,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_1323,c_2282]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5569,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_5560]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_50832,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k7_subset_1(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_50284,c_5569]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_51462,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_50832,c_5,c_14087]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_59284,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_51462]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_59850,plain,
% 31.70/4.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_59284]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_80514,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_79675,c_59850]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_80518,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_80514,c_6]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_97578,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_80518,c_59850]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_97813,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_97578,c_6,c_2284,c_9613]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_773,plain,
% 31.70/4.50      ( l1_pre_topc(sK0) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_784,plain,
% 31.70/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.70/4.50      | r1_tarski(X0,X1) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_18,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ l1_pre_topc(X1)
% 31.70/4.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 31.70/4.50      inference(cnf_transformation,[],[f62]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_777,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_3584,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 31.70/4.50      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_784,c_777]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_12442,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(X0),k4_xboole_0(u1_struct_0(X0),X1),k2_tops_1(X0,k4_xboole_0(u1_struct_0(X0),X1))) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_785,c_3584]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_37897,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X0)) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_773,c_12442]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_110520,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))))) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0)))
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_97813,c_37897]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_110578,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))))) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X0))
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_110520,c_37897]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_112199,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X0))
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_84393,c_110578]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_942,plain,
% 31.70/4.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.70/4.50      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_12]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_15,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ l1_pre_topc(X1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f59]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_963,plain,
% 31.70/4.50      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.70/4.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.70/4.50      | ~ l1_pre_topc(sK0) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_15]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1044,plain,
% 31.70/4.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.70/4.50      | ~ l1_pre_topc(sK0)
% 31.70/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_18]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1122,plain,
% 31.70/4.50      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.70/4.50      | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_12]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_259,plain,( X0 = X0 ),theory(equality) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1168,plain,
% 31.70/4.50      ( sK1 = sK1 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_259]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1433,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_259]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.70/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.70/4.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.70/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_188,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.70/4.50      | ~ r1_tarski(X2,X1)
% 31.70/4.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.70/4.50      inference(bin_hyper_res,[status(thm)],[c_9,c_144]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_370,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.70/4.50      inference(prop_impl,[status(thm)],[c_11]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_371,plain,
% 31.70/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_370]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_443,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,X1)
% 31.70/4.50      | ~ r1_tarski(X2,X1)
% 31.70/4.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.70/4.50      inference(bin_hyper_res,[status(thm)],[c_188,c_371]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1117,plain,
% 31.70/4.50      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 31.70/4.50      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 31.70/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_443]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1520,plain,
% 31.70/4.50      ( ~ r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
% 31.70/4.50      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 31.70/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_1117]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_260,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1434,plain,
% 31.70/4.50      ( X0 != X1
% 31.70/4.50      | k2_pre_topc(sK0,sK1) != X1
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = X0 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_260]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2682,plain,
% 31.70/4.50      ( X0 != k2_pre_topc(sK0,sK1)
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = X0
% 31.70/4.50      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_1434]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4827,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k2_pre_topc(sK0,sK1)
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_2682]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2919,plain,
% 31.70/4.50      ( X0 != X1
% 31.70/4.50      | X0 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != X1 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_260]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6095,plain,
% 31.70/4.50      ( X0 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | X0 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_2919]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9175,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_6095]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9176,plain,
% 31.70/4.50      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_259]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9750,plain,
% 31.70/4.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_9613,c_5]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_9753,plain,
% 31.70/4.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_9750,c_3]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_14877,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_14125,c_9753]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6987,plain,
% 31.70/4.50      ( X0 != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = X0
% 31.70/4.50      | k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_1434]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_25892,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_6987]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1153,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) != X0
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | sK1 != X0 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_260]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_40119,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | k2_pre_topc(sK0,sK1) = sK1
% 31.70/4.50      | sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_1153]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1566,plain,
% 31.70/4.50      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_260]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2707,plain,
% 31.70/4.50      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_1566]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_114434,plain,
% 31.70/4.50      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != sK1
% 31.70/4.50      | sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
% 31.70/4.50      | sK1 != sK1 ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_2707]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_114546,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_112199,c_22,c_21,c_942,c_963,c_1044,c_1122,c_1168,
% 31.70/4.50                 c_1433,c_1520,c_4827,c_9175,c_9176,c_14877,c_25892,
% 31.70/4.50                 c_40119,c_114434]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_17,plain,
% 31.70/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ l1_pre_topc(X1)
% 31.70/4.50      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 31.70/4.50      inference(cnf_transformation,[],[f61]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_778,plain,
% 31.70/4.50      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1973,plain,
% 31.70/4.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.70/4.50      | l1_pre_topc(sK0) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_774,c_778]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_1052,plain,
% 31.70/4.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.70/4.50      | ~ l1_pre_topc(sK0)
% 31.70/4.50      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.70/4.50      inference(instantiation,[status(thm)],[c_17]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_2299,plain,
% 31.70/4.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_1973,c_22,c_21,c_1052]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_114551,plain,
% 31.70/4.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_114546,c_2299]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4858,plain,
% 31.70/4.50      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3462,c_771]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_4507,plain,
% 31.70/4.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_3462,c_770]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_5187,plain,
% 31.70/4.50      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_4858,c_4507]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6395,plain,
% 31.70/4.50      ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_4857,c_5187]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_12445,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(X0),k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))),k2_tops_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))))) = k2_pre_topc(X0,k4_xboole_0(X1,k4_xboole_0(X1,u1_struct_0(X0))))
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1321,c_3584]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_41356,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k2_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))))) = k2_pre_topc(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_773,c_12445]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_38750,plain,
% 31.70/4.50      ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k2_tops_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))))) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_1,c_37897]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_41691,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_41356,c_38750]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_13,plain,
% 31.70/4.50      ( v4_pre_topc(X0,X1)
% 31.70/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.70/4.50      | ~ l1_pre_topc(X1)
% 31.70/4.50      | ~ v2_pre_topc(X1)
% 31.70/4.50      | k2_pre_topc(X1,X0) != X0 ),
% 31.70/4.50      inference(cnf_transformation,[],[f58]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_782,plain,
% 31.70/4.50      ( k2_pre_topc(X0,X1) != X1
% 31.70/4.50      | v4_pre_topc(X1,X0) = iProver_top
% 31.70/4.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.70/4.50      | l1_pre_topc(X0) != iProver_top
% 31.70/4.50      | v2_pre_topc(X0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_42113,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) != k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))
% 31.70/4.50      | v4_pre_topc(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),sK0) = iProver_top
% 31.70/4.50      | m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.70/4.50      | l1_pre_topc(sK0) != iProver_top
% 31.70/4.50      | v2_pre_topc(sK0) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_41691,c_782]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_23,negated_conjecture,
% 31.70/4.50      ( v2_pre_topc(sK0) ),
% 31.70/4.50      inference(cnf_transformation,[],[f63]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_24,plain,
% 31.70/4.50      ( v2_pre_topc(sK0) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_43727,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) != k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0)))
% 31.70/4.50      | v4_pre_topc(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),sK0) = iProver_top
% 31.70/4.50      | m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_42113,c_24,c_25]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_43740,plain,
% 31.70/4.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) != k2_pre_topc(sK0,sK1)
% 31.70/4.50      | v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))),sK0) = iProver_top
% 31.70/4.50      | m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6395,c_43727]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6436,plain,
% 31.70/4.50      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 31.70/4.50      inference(superposition,[status(thm)],[c_6395,c_1322]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_6441,plain,
% 31.70/4.50      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_6436,c_2943]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_43811,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) != k4_xboole_0(sK1,k1_xboole_0)
% 31.70/4.50      | v4_pre_topc(k4_xboole_0(sK1,k1_xboole_0),sK0) = iProver_top
% 31.70/4.50      | m1_subset_1(k4_xboole_0(sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.70/4.50      inference(light_normalisation,[status(thm)],[c_43740,c_6441]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_43812,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) != sK1
% 31.70/4.50      | v4_pre_topc(sK1,sK0) = iProver_top
% 31.70/4.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.70/4.50      inference(demodulation,[status(thm)],[c_43811,c_6]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_26,plain,
% 31.70/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_63300,plain,
% 31.70/4.50      ( v4_pre_topc(sK1,sK0) = iProver_top
% 31.70/4.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 31.70/4.50      inference(global_propositional_subsumption,
% 31.70/4.50                [status(thm)],
% 31.70/4.50                [c_43812,c_26]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_63301,plain,
% 31.70/4.50      ( k2_pre_topc(sK0,sK1) != sK1
% 31.70/4.50      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 31.70/4.50      inference(renaming,[status(thm)],[c_63300]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_19,negated_conjecture,
% 31.70/4.50      ( ~ v4_pre_topc(sK1,sK0)
% 31.70/4.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 31.70/4.50      inference(cnf_transformation,[],[f67]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(c_28,plain,
% 31.70/4.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 31.70/4.50      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.70/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.70/4.50  
% 31.70/4.50  cnf(contradiction,plain,
% 31.70/4.50      ( $false ),
% 31.70/4.50      inference(minisat,[status(thm)],[c_114551,c_114546,c_63301,c_28]) ).
% 31.70/4.50  
% 31.70/4.50  
% 31.70/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.70/4.50  
% 31.70/4.50  ------                               Statistics
% 31.70/4.50  
% 31.70/4.50  ------ Selected
% 31.70/4.50  
% 31.70/4.50  total_time:                             3.722
% 31.70/4.50  
%------------------------------------------------------------------------------

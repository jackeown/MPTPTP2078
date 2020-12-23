%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:58 EST 2020

% Result     : Theorem 39.64s
% Output     : CNFRefutation 39.64s
% Verified   : 
% Statistics : Number of formulae       :  274 (1891 expanded)
%              Number of clauses        :  186 ( 576 expanded)
%              Number of leaves         :   25 ( 434 expanded)
%              Depth                    :   22
%              Number of atoms          :  799 (6804 expanded)
%              Number of equality atoms :  369 (1771 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1))
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1))
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1))
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,sK1))
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1))
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,X1))
          & v4_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f58,f57])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f70,f63])).

fof(f86,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f65,f63])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f64,f63])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_854,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_864,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_870,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3940,plain,
    ( k5_xboole_0(k1_tops_1(X0,X1),k3_xboole_0(k1_tops_1(X0,X1),X2)) = k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_864,c_870])).

cnf(c_37827,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_3940])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1129,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_37863,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37827,c_27,c_26,c_1129,c_1358])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_877,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_876,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1498,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_876])).

cnf(c_37947,plain,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_37863,c_1498])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_875,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1241,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_875])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_872,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7574,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_872])).

cnf(c_50858,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_7574])).

cnf(c_51032,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),X0)) = k1_xboole_0
    | r1_xboole_0(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37863,c_50858])).

cnf(c_51045,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k1_xboole_0
    | r1_xboole_0(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_51032,c_37863])).

cnf(c_51744,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_37947,c_51045])).

cnf(c_37925,plain,
    ( r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X1)) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_37863,c_875])).

cnf(c_56903,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_51744,c_37925])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_863,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_861,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3023,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,k2_tops_1(X0,X1))) = k1_tops_1(X0,k2_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_861])).

cnf(c_11668,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_3023])).

cnf(c_1132,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1455,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_12314,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11668,c_27,c_26,c_1132,c_1455])).

cnf(c_13,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_866,plain,
    ( v4_tops_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_873,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6783,plain,
    ( v4_tops_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X0)),X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_873])).

cnf(c_125327,plain,
    ( v4_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12314,c_6783])).

cnf(c_30,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1133,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_1458,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1465,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2369,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2373,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2369])).

cnf(c_11018,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_29991,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
    | ~ r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) ),
    inference(instantiation,[status(thm)],[c_11018])).

cnf(c_29992,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29991])).

cnf(c_126350,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_125327,c_30,c_31,c_1133,c_1465,c_2373,c_29992])).

cnf(c_126351,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_126350])).

cnf(c_126362,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_56903,c_126351])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1123,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1124,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_2997,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3000,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2997])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_871,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4240,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k2_xboole_0(X1,k2_tops_1(X0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_871])).

cnf(c_65468,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_4240])).

cnf(c_66623,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_65468,c_30])).

cnf(c_66624,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_66623])).

cnf(c_66634,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_854,c_66624])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_857,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2649,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_857])).

cnf(c_1224,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3493,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2649,c_27,c_26,c_1224])).

cnf(c_66636,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_66634,c_3493])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_856,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3025,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_tops_1(X0,k2_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_856])).

cnf(c_13963,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_3025])).

cnf(c_1453,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_14513,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13963,c_27,c_26,c_1132,c_1453])).

cnf(c_3028,plain,
    ( k5_xboole_0(k2_tops_1(X0,X1),k3_xboole_0(k2_tops_1(X0,X1),X2)) = k7_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_870])).

cnf(c_18492,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_3028])).

cnf(c_1439,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_19645,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18492,c_27,c_26,c_1132,c_1439])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_874,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7570,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_873])).

cnf(c_7896,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7570,c_873])).

cnf(c_22468,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X1),X3) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X4)),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_7896])).

cnf(c_64468,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X2)),k2_xboole_0(X3,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_22468])).

cnf(c_65516,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0),k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_19645,c_64468])).

cnf(c_67223,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14513,c_65516])).

cnf(c_67303,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_66636,c_67223])).

cnf(c_869,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4162,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) = k1_tops_1(X0,k2_pre_topc(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_861])).

cnf(c_42547,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_4162])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_42798,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42547,c_27,c_26,c_1123,c_1324])).

cnf(c_125326,plain,
    ( v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_42798,c_6783])).

cnf(c_1327,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1334,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_1767,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1771,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1767])).

cnf(c_10495,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_29731,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) ),
    inference(instantiation,[status(thm)],[c_10495])).

cnf(c_29732,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29731])).

cnf(c_126099,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_125326,c_30,c_31,c_1124,c_1334,c_1771,c_29732])).

cnf(c_126100,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_126099])).

cnf(c_126111,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_56903,c_126100])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_29,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_32,plain,
    ( v4_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1221,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1222,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1221])).

cnf(c_17,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1318,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1319,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_21,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1630,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_10521,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_10522,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10521])).

cnf(c_155854,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_126111,c_29,c_30,c_31,c_32,c_1124,c_1222,c_1319,c_1334,c_10522])).

cnf(c_3017,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_861])).

cnf(c_1172,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3449,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3017,c_27,c_26,c_1172])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_859,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5848,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3449,c_859])).

cnf(c_1130,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_8291,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5848,c_30,c_31,c_1130])).

cnf(c_8292,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8291])).

cnf(c_5847,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3449,c_859])).

cnf(c_8230,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5847,c_30,c_31,c_1130])).

cnf(c_8231,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8230])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_878,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8241,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8231,c_878])).

cnf(c_17476,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8292,c_8241])).

cnf(c_2796,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | X0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2797,plain,
    ( X0 = k1_tops_1(sK0,sK1)
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2796])).

cnf(c_389,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3214,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1403,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k1_tops_1(sK0,sK1)
    | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_8419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k1_tops_1(sK0,sK1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_8421,plain,
    ( X0 != k1_tops_1(sK0,sK1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8419])).

cnf(c_17538,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17476,c_30,c_31,c_1130,c_2797,c_3214,c_8421])).

cnf(c_155871,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,sK1)
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_155854,c_17538])).

cnf(c_155903,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_155871,c_42798])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2882,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_19604,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2796])).

cnf(c_156044,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_155903,c_28,c_27,c_26,c_25,c_1123,c_1126,c_1221,c_1318,c_1327,c_2882,c_10521,c_19604])).

cnf(c_12318,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12314,c_859])).

cnf(c_1449,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1450,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) = iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_2226,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2232,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2226])).

cnf(c_12360,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12318,c_30,c_31,c_1133,c_1465])).

cnf(c_12361,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12360])).

cnf(c_156210,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_156044,c_12361])).

cnf(c_163139,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_126362,c_30,c_31,c_1124,c_3000,c_67303,c_156210])).

cnf(c_1568,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_854,c_870])).

cnf(c_1493,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_856])).

cnf(c_1227,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1885,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_27,c_26,c_1227])).

cnf(c_1888,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1568,c_1885])).

cnf(c_1892,plain,
    ( r1_xboole_0(X0,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_876])).

cnf(c_163159,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_163139,c_1892])).

cnf(c_19660,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19645,c_1241])).

cnf(c_19979,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14513,c_19660])).

cnf(c_20380,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0
    | r1_xboole_0(X0,k2_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19979,c_872])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_390,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1138,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_1547,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
    | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_1548,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_31765,plain,
    ( r1_xboole_0(X0,k2_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20380,c_24,c_1547,c_1548])).

cnf(c_31773,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_31765])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_163159,c_31773])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 39.64/5.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.64/5.50  
% 39.64/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.64/5.50  
% 39.64/5.50  ------  iProver source info
% 39.64/5.50  
% 39.64/5.50  git: date: 2020-06-30 10:37:57 +0100
% 39.64/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.64/5.50  git: non_committed_changes: false
% 39.64/5.50  git: last_make_outside_of_git: false
% 39.64/5.50  
% 39.64/5.50  ------ 
% 39.64/5.50  ------ Parsing...
% 39.64/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.64/5.50  
% 39.64/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 39.64/5.50  
% 39.64/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.64/5.50  
% 39.64/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.64/5.50  ------ Proving...
% 39.64/5.50  ------ Problem Properties 
% 39.64/5.50  
% 39.64/5.50  
% 39.64/5.50  clauses                                 28
% 39.64/5.50  conjectures                             5
% 39.64/5.50  EPR                                     7
% 39.64/5.50  Horn                                    28
% 39.64/5.50  unary                                   6
% 39.64/5.50  binary                                  4
% 39.64/5.50  lits                                    79
% 39.64/5.50  lits eq                                 8
% 39.64/5.50  fd_pure                                 0
% 39.64/5.50  fd_pseudo                               0
% 39.64/5.50  fd_cond                                 1
% 39.64/5.50  fd_pseudo_cond                          1
% 39.64/5.50  AC symbols                              0
% 39.64/5.50  
% 39.64/5.50  ------ Input Options Time Limit: Unbounded
% 39.64/5.50  
% 39.64/5.50  
% 39.64/5.50  ------ 
% 39.64/5.50  Current options:
% 39.64/5.50  ------ 
% 39.64/5.50  
% 39.64/5.50  
% 39.64/5.50  
% 39.64/5.50  
% 39.64/5.50  ------ Proving...
% 39.64/5.50  
% 39.64/5.50  
% 39.64/5.50  % SZS status Theorem for theBenchmark.p
% 39.64/5.50  
% 39.64/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 39.64/5.50  
% 39.64/5.50  fof(f21,conjecture,(
% 39.64/5.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,X1)))))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f22,negated_conjecture,(
% 39.64/5.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,X1)))))),
% 39.64/5.50    inference(negated_conjecture,[],[f21])).
% 39.64/5.50  
% 39.64/5.50  fof(f51,plain,(
% 39.64/5.50    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1)) & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 39.64/5.50    inference(ennf_transformation,[],[f22])).
% 39.64/5.50  
% 39.64/5.50  fof(f52,plain,(
% 39.64/5.50    ? [X0] : (? [X1] : (k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f51])).
% 39.64/5.50  
% 39.64/5.50  fof(f58,plain,(
% 39.64/5.50    ( ! [X0] : (? [X1] : (k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,sK1)) & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.64/5.50    introduced(choice_axiom,[])).
% 39.64/5.50  
% 39.64/5.50  fof(f57,plain,(
% 39.64/5.50    ? [X0] : (? [X1] : (k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,X1)) & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 39.64/5.50    introduced(choice_axiom,[])).
% 39.64/5.50  
% 39.64/5.50  fof(f59,plain,(
% 39.64/5.50    (k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 39.64/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f58,f57])).
% 39.64/5.50  
% 39.64/5.50  fof(f87,plain,(
% 39.64/5.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.64/5.50    inference(cnf_transformation,[],[f59])).
% 39.64/5.50  
% 39.64/5.50  fof(f12,axiom,(
% 39.64/5.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f36,plain,(
% 39.64/5.50    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.64/5.50    inference(ennf_transformation,[],[f12])).
% 39.64/5.50  
% 39.64/5.50  fof(f37,plain,(
% 39.64/5.50    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f36])).
% 39.64/5.50  
% 39.64/5.50  fof(f76,plain,(
% 39.64/5.50    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f37])).
% 39.64/5.50  
% 39.64/5.50  fof(f8,axiom,(
% 39.64/5.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f31,plain,(
% 39.64/5.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.64/5.50    inference(ennf_transformation,[],[f8])).
% 39.64/5.50  
% 39.64/5.50  fof(f70,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.64/5.50    inference(cnf_transformation,[],[f31])).
% 39.64/5.50  
% 39.64/5.50  fof(f2,axiom,(
% 39.64/5.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f63,plain,(
% 39.64/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.64/5.50    inference(cnf_transformation,[],[f2])).
% 39.64/5.50  
% 39.64/5.50  fof(f92,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.64/5.50    inference(definition_unfolding,[],[f70,f63])).
% 39.64/5.50  
% 39.64/5.50  fof(f86,plain,(
% 39.64/5.50    l1_pre_topc(sK0)),
% 39.64/5.50    inference(cnf_transformation,[],[f59])).
% 39.64/5.50  
% 39.64/5.50  fof(f1,axiom,(
% 39.64/5.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f53,plain,(
% 39.64/5.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.64/5.50    inference(nnf_transformation,[],[f1])).
% 39.64/5.50  
% 39.64/5.50  fof(f54,plain,(
% 39.64/5.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.64/5.50    inference(flattening,[],[f53])).
% 39.64/5.50  
% 39.64/5.50  fof(f60,plain,(
% 39.64/5.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.64/5.50    inference(cnf_transformation,[],[f54])).
% 39.64/5.50  
% 39.64/5.50  fof(f94,plain,(
% 39.64/5.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.64/5.50    inference(equality_resolution,[],[f60])).
% 39.64/5.50  
% 39.64/5.50  fof(f3,axiom,(
% 39.64/5.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f23,plain,(
% 39.64/5.50    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 39.64/5.50    inference(ennf_transformation,[],[f3])).
% 39.64/5.50  
% 39.64/5.50  fof(f65,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 39.64/5.50    inference(cnf_transformation,[],[f23])).
% 39.64/5.50  
% 39.64/5.50  fof(f90,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 39.64/5.50    inference(definition_unfolding,[],[f65,f63])).
% 39.64/5.50  
% 39.64/5.50  fof(f64,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 39.64/5.50    inference(cnf_transformation,[],[f23])).
% 39.64/5.50  
% 39.64/5.50  fof(f91,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 39.64/5.50    inference(definition_unfolding,[],[f64,f63])).
% 39.64/5.50  
% 39.64/5.50  fof(f6,axiom,(
% 39.64/5.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f27,plain,(
% 39.64/5.50    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 39.64/5.50    inference(ennf_transformation,[],[f6])).
% 39.64/5.50  
% 39.64/5.50  fof(f28,plain,(
% 39.64/5.50    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 39.64/5.50    inference(flattening,[],[f27])).
% 39.64/5.50  
% 39.64/5.50  fof(f68,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f28])).
% 39.64/5.50  
% 39.64/5.50  fof(f13,axiom,(
% 39.64/5.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f38,plain,(
% 39.64/5.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.64/5.50    inference(ennf_transformation,[],[f13])).
% 39.64/5.50  
% 39.64/5.50  fof(f39,plain,(
% 39.64/5.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f38])).
% 39.64/5.50  
% 39.64/5.50  fof(f77,plain,(
% 39.64/5.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f39])).
% 39.64/5.50  
% 39.64/5.50  fof(f15,axiom,(
% 39.64/5.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f42,plain,(
% 39.64/5.50    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.64/5.50    inference(ennf_transformation,[],[f15])).
% 39.64/5.50  
% 39.64/5.50  fof(f43,plain,(
% 39.64/5.50    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f42])).
% 39.64/5.50  
% 39.64/5.50  fof(f79,plain,(
% 39.64/5.50    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f43])).
% 39.64/5.50  
% 39.64/5.50  fof(f11,axiom,(
% 39.64/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f35,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(ennf_transformation,[],[f11])).
% 39.64/5.50  
% 39.64/5.50  fof(f55,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(nnf_transformation,[],[f35])).
% 39.64/5.50  
% 39.64/5.50  fof(f56,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f55])).
% 39.64/5.50  
% 39.64/5.50  fof(f74,plain,(
% 39.64/5.50    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f56])).
% 39.64/5.50  
% 39.64/5.50  fof(f5,axiom,(
% 39.64/5.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f25,plain,(
% 39.64/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 39.64/5.50    inference(ennf_transformation,[],[f5])).
% 39.64/5.50  
% 39.64/5.50  fof(f26,plain,(
% 39.64/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 39.64/5.50    inference(flattening,[],[f25])).
% 39.64/5.50  
% 39.64/5.50  fof(f67,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f26])).
% 39.64/5.50  
% 39.64/5.50  fof(f10,axiom,(
% 39.64/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f34,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(ennf_transformation,[],[f10])).
% 39.64/5.50  
% 39.64/5.50  fof(f72,plain,(
% 39.64/5.50    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f34])).
% 39.64/5.50  
% 39.64/5.50  fof(f9,axiom,(
% 39.64/5.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f32,plain,(
% 39.64/5.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.64/5.50    inference(ennf_transformation,[],[f9])).
% 39.64/5.50  
% 39.64/5.50  fof(f33,plain,(
% 39.64/5.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f32])).
% 39.64/5.50  
% 39.64/5.50  fof(f71,plain,(
% 39.64/5.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f33])).
% 39.64/5.50  
% 39.64/5.50  fof(f7,axiom,(
% 39.64/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f29,plain,(
% 39.64/5.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 39.64/5.50    inference(ennf_transformation,[],[f7])).
% 39.64/5.50  
% 39.64/5.50  fof(f30,plain,(
% 39.64/5.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.64/5.50    inference(flattening,[],[f29])).
% 39.64/5.50  
% 39.64/5.50  fof(f69,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.64/5.50    inference(cnf_transformation,[],[f30])).
% 39.64/5.50  
% 39.64/5.50  fof(f19,axiom,(
% 39.64/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f49,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(ennf_transformation,[],[f19])).
% 39.64/5.50  
% 39.64/5.50  fof(f83,plain,(
% 39.64/5.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f49])).
% 39.64/5.50  
% 39.64/5.50  fof(f20,axiom,(
% 39.64/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f50,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(ennf_transformation,[],[f20])).
% 39.64/5.50  
% 39.64/5.50  fof(f84,plain,(
% 39.64/5.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f50])).
% 39.64/5.50  
% 39.64/5.50  fof(f4,axiom,(
% 39.64/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f24,plain,(
% 39.64/5.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 39.64/5.50    inference(ennf_transformation,[],[f4])).
% 39.64/5.50  
% 39.64/5.50  fof(f66,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f24])).
% 39.64/5.50  
% 39.64/5.50  fof(f85,plain,(
% 39.64/5.50    v2_pre_topc(sK0)),
% 39.64/5.50    inference(cnf_transformation,[],[f59])).
% 39.64/5.50  
% 39.64/5.50  fof(f88,plain,(
% 39.64/5.50    v4_tops_1(sK1,sK0)),
% 39.64/5.50    inference(cnf_transformation,[],[f59])).
% 39.64/5.50  
% 39.64/5.50  fof(f73,plain,(
% 39.64/5.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f56])).
% 39.64/5.50  
% 39.64/5.50  fof(f14,axiom,(
% 39.64/5.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f40,plain,(
% 39.64/5.50    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 39.64/5.50    inference(ennf_transformation,[],[f14])).
% 39.64/5.50  
% 39.64/5.50  fof(f41,plain,(
% 39.64/5.50    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f40])).
% 39.64/5.50  
% 39.64/5.50  fof(f78,plain,(
% 39.64/5.50    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f41])).
% 39.64/5.50  
% 39.64/5.50  fof(f18,axiom,(
% 39.64/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f47,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(ennf_transformation,[],[f18])).
% 39.64/5.50  
% 39.64/5.50  fof(f48,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f47])).
% 39.64/5.50  
% 39.64/5.50  fof(f82,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f48])).
% 39.64/5.50  
% 39.64/5.50  fof(f17,axiom,(
% 39.64/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 39.64/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.64/5.50  
% 39.64/5.50  fof(f45,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(ennf_transformation,[],[f17])).
% 39.64/5.50  
% 39.64/5.50  fof(f46,plain,(
% 39.64/5.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.64/5.50    inference(flattening,[],[f45])).
% 39.64/5.50  
% 39.64/5.50  fof(f81,plain,(
% 39.64/5.50    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f46])).
% 39.64/5.50  
% 39.64/5.50  fof(f62,plain,(
% 39.64/5.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 39.64/5.50    inference(cnf_transformation,[],[f54])).
% 39.64/5.50  
% 39.64/5.50  fof(f89,plain,(
% 39.64/5.50    k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1))),
% 39.64/5.50    inference(cnf_transformation,[],[f59])).
% 39.64/5.50  
% 39.64/5.50  cnf(c_26,negated_conjecture,
% 39.64/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.64/5.50      inference(cnf_transformation,[],[f87]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_854,plain,
% 39.64/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_15,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ l1_pre_topc(X1) ),
% 39.64/5.50      inference(cnf_transformation,[],[f76]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_864,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 39.64/5.50      | l1_pre_topc(X1) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_9,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.64/5.50      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 39.64/5.50      inference(cnf_transformation,[],[f92]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_870,plain,
% 39.64/5.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3940,plain,
% 39.64/5.50      ( k5_xboole_0(k1_tops_1(X0,X1),k3_xboole_0(k1_tops_1(X0,X1),X2)) = k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),X2)
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_864,c_870]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_37827,plain,
% 39.64/5.50      ( k5_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0)
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_3940]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_27,negated_conjecture,
% 39.64/5.50      ( l1_pre_topc(sK0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f86]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1129,plain,
% 39.64/5.50      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_15]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1358,plain,
% 39.64/5.50      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | k5_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_9]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_37863,plain,
% 39.64/5.50      ( k5_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_37827,c_27,c_26,c_1129,c_1358]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2,plain,
% 39.64/5.50      ( r1_tarski(X0,X0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f94]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_877,plain,
% 39.64/5.50      ( r1_tarski(X0,X0) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3,plain,
% 39.64/5.50      ( r1_xboole_0(X0,X1)
% 39.64/5.50      | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 39.64/5.50      inference(cnf_transformation,[],[f90]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_876,plain,
% 39.64/5.50      ( r1_xboole_0(X0,X1) = iProver_top
% 39.64/5.50      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1498,plain,
% 39.64/5.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_877,c_876]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_37947,plain,
% 39.64/5.50      ( r1_xboole_0(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0),X0) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_37863,c_1498]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_4,plain,
% 39.64/5.50      ( r1_tarski(X0,X1)
% 39.64/5.50      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 39.64/5.50      inference(cnf_transformation,[],[f91]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_875,plain,
% 39.64/5.50      ( r1_tarski(X0,X1) = iProver_top
% 39.64/5.50      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1241,plain,
% 39.64/5.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_877,c_875]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_7,plain,
% 39.64/5.50      ( ~ r1_xboole_0(X0,X1)
% 39.64/5.50      | ~ r1_tarski(X2,X0)
% 39.64/5.50      | ~ r1_tarski(X2,X1)
% 39.64/5.50      | k1_xboole_0 = X2 ),
% 39.64/5.50      inference(cnf_transformation,[],[f68]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_872,plain,
% 39.64/5.50      ( k1_xboole_0 = X0
% 39.64/5.50      | r1_xboole_0(X1,X2) != iProver_top
% 39.64/5.50      | r1_tarski(X0,X1) != iProver_top
% 39.64/5.50      | r1_tarski(X0,X2) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_7574,plain,
% 39.64/5.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 39.64/5.50      | r1_xboole_0(X2,X0) != iProver_top
% 39.64/5.50      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_1241,c_872]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_50858,plain,
% 39.64/5.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 39.64/5.50      | r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_877,c_7574]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_51032,plain,
% 39.64/5.50      ( k5_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),X0)) = k1_xboole_0
% 39.64/5.50      | r1_xboole_0(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,sK1)) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_37863,c_50858]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_51045,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k1_xboole_0
% 39.64/5.50      | r1_xboole_0(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,sK1)) != iProver_top ),
% 39.64/5.50      inference(demodulation,[status(thm)],[c_51032,c_37863]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_51744,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_37947,c_51045]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_37925,plain,
% 39.64/5.50      ( r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X1)) != iProver_top
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_37863,c_875]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_56903,plain,
% 39.64/5.50      ( r1_tarski(X0,k1_tops_1(sK0,sK1)) = iProver_top
% 39.64/5.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_51744,c_37925]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_16,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ l1_pre_topc(X1) ),
% 39.64/5.50      inference(cnf_transformation,[],[f77]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_863,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.64/5.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 39.64/5.50      | l1_pre_topc(X1) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_18,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ l1_pre_topc(X1)
% 39.64/5.50      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f79]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_861,plain,
% 39.64/5.50      ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3023,plain,
% 39.64/5.50      ( k1_tops_1(X0,k1_tops_1(X0,k2_tops_1(X0,X1))) = k1_tops_1(X0,k2_tops_1(X0,X1))
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_863,c_861]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_11668,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_3023]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1132,plain,
% 39.64/5.50      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_16]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1455,plain,
% 39.64/5.50      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0)
% 39.64/5.50      | k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_18]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_12314,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_11668,c_27,c_26,c_1132,c_1455]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_13,plain,
% 39.64/5.50      ( ~ v4_tops_1(X0,X1)
% 39.64/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 39.64/5.50      | ~ l1_pre_topc(X1) ),
% 39.64/5.50      inference(cnf_transformation,[],[f74]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_866,plain,
% 39.64/5.50      ( v4_tops_1(X0,X1) != iProver_top
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.64/5.50      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) = iProver_top
% 39.64/5.50      | l1_pre_topc(X1) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_6,plain,
% 39.64/5.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 39.64/5.50      inference(cnf_transformation,[],[f67]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_873,plain,
% 39.64/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.64/5.50      | r1_tarski(X1,X2) != iProver_top
% 39.64/5.50      | r1_tarski(X0,X2) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_6783,plain,
% 39.64/5.50      ( v4_tops_1(X0,X1) != iProver_top
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.64/5.50      | r1_tarski(X0,X2) = iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X0)),X2) != iProver_top
% 39.64/5.50      | l1_pre_topc(X1) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_866,c_873]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_125327,plain,
% 39.64/5.50      ( v4_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_12314,c_6783]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_30,plain,
% 39.64/5.50      ( l1_pre_topc(sK0) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_31,plain,
% 39.64/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1133,plain,
% 39.64/5.50      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 39.64/5.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1458,plain,
% 39.64/5.50      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_15]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1465,plain,
% 39.64/5.50      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_11,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 39.64/5.50      | ~ l1_pre_topc(X1) ),
% 39.64/5.50      inference(cnf_transformation,[],[f72]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2369,plain,
% 39.64/5.50      ( ~ m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_11]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2373,plain,
% 39.64/5.50      ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_2369]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_11018,plain,
% 39.64/5.50      ( ~ r1_tarski(X0,X1)
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X1) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_6]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_29991,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))))
% 39.64/5.50      | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_11018]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_29992,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))) != iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_29991]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_126350,plain,
% 39.64/5.50      ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_125327,c_30,c_31,c_1133,c_1465,c_2373,c_29992]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_126351,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) != iProver_top ),
% 39.64/5.50      inference(renaming,[status(thm)],[c_126350]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_126362,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_56903,c_126351]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_10,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ l1_pre_topc(X1) ),
% 39.64/5.50      inference(cnf_transformation,[],[f71]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1123,plain,
% 39.64/5.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_10]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1124,plain,
% 39.64/5.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 39.64/5.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2997,plain,
% 39.64/5.50      ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_2]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3000,plain,
% 39.64/5.50      ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_2997]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_8,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.64/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.64/5.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f69]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_871,plain,
% 39.64/5.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 39.64/5.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_4240,plain,
% 39.64/5.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k2_xboole_0(X1,k2_tops_1(X0,X2))
% 39.64/5.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_863,c_871]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_65468,plain,
% 39.64/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_4240]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_66623,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_65468,c_30]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_66624,plain,
% 39.64/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.64/5.50      inference(renaming,[status(thm)],[c_66623]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_66634,plain,
% 39.64/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_66624]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_22,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ l1_pre_topc(X1)
% 39.64/5.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f83]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_857,plain,
% 39.64/5.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2649,plain,
% 39.64/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_857]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1224,plain,
% 39.64/5.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0)
% 39.64/5.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_22]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3493,plain,
% 39.64/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_2649,c_27,c_26,c_1224]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_66636,plain,
% 39.64/5.50      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.64/5.50      inference(light_normalisation,[status(thm)],[c_66634,c_3493]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_23,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ l1_pre_topc(X1)
% 39.64/5.50      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f84]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_856,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3025,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_tops_1(X0,k2_tops_1(X0,X1))
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_863,c_856]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_13963,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_3025]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1453,plain,
% 39.64/5.50      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0)
% 39.64/5.50      | k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_23]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_14513,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_13963,c_27,c_26,c_1132,c_1453]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3028,plain,
% 39.64/5.50      ( k5_xboole_0(k2_tops_1(X0,X1),k3_xboole_0(k2_tops_1(X0,X1),X2)) = k7_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),X2)
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_863,c_870]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_18492,plain,
% 39.64/5.50      ( k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_3028]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1439,plain,
% 39.64/5.50      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_9]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_19645,plain,
% 39.64/5.50      ( k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_18492,c_27,c_26,c_1132,c_1439]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_5,plain,
% 39.64/5.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 39.64/5.50      inference(cnf_transformation,[],[f66]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_874,plain,
% 39.64/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.64/5.50      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_7570,plain,
% 39.64/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.64/5.50      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_1241,c_873]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_7896,plain,
% 39.64/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.64/5.50      | r1_tarski(X1,X2) != iProver_top
% 39.64/5.50      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X2) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_7570,c_873]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_22468,plain,
% 39.64/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.64/5.50      | r1_tarski(k2_xboole_0(X2,X1),X3) != iProver_top
% 39.64/5.50      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X4)),X3) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_874,c_7896]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_64468,plain,
% 39.64/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.64/5.50      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X2)),k2_xboole_0(X3,X1)) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_877,c_22468]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_65516,plain,
% 39.64/5.50      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0),k2_xboole_0(X1,X2)) = iProver_top
% 39.64/5.50      | r1_tarski(k2_tops_1(sK0,sK1),X2) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_19645,c_64468]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_67223,plain,
% 39.64/5.50      ( r1_tarski(k2_tops_1(sK0,sK1),X0) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_xboole_0(X1,X0)) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_14513,c_65516]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_67303,plain,
% 39.64/5.50      ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_66636,c_67223]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_869,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.64/5.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 39.64/5.50      | l1_pre_topc(X1) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_4162,plain,
% 39.64/5.50      ( k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) = k1_tops_1(X0,k2_pre_topc(X0,X1))
% 39.64/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_869,c_861]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_42547,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_4162]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1324,plain,
% 39.64/5.50      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0)
% 39.64/5.50      | k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_18]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_42798,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_42547,c_27,c_26,c_1123,c_1324]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_125326,plain,
% 39.64/5.50      ( v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) = iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_42798,c_6783]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1327,plain,
% 39.64/5.50      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_15]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1334,plain,
% 39.64/5.50      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 39.64/5.50      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1327]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1767,plain,
% 39.64/5.50      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_11]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1771,plain,
% 39.64/5.50      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1767]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_10495,plain,
% 39.64/5.50      ( ~ r1_tarski(X0,X1)
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0)
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X1) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_6]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_29731,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0)
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 39.64/5.50      | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_10495]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_29732,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) = iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_29731]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_126099,plain,
% 39.64/5.50      ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) = iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_125326,c_30,c_31,c_1124,c_1334,c_1771,c_29732]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_126100,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) = iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top ),
% 39.64/5.50      inference(renaming,[status(thm)],[c_126099]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_126111,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
% 39.64/5.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_xboole_0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_56903,c_126100]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_28,negated_conjecture,
% 39.64/5.50      ( v2_pre_topc(sK0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f85]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_29,plain,
% 39.64/5.50      ( v2_pre_topc(sK0) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_25,negated_conjecture,
% 39.64/5.50      ( v4_tops_1(sK1,sK0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f88]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_32,plain,
% 39.64/5.50      ( v4_tops_1(sK1,sK0) = iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_14,plain,
% 39.64/5.50      ( ~ v4_tops_1(X0,X1)
% 39.64/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 39.64/5.50      | ~ l1_pre_topc(X1) ),
% 39.64/5.50      inference(cnf_transformation,[],[f73]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1221,plain,
% 39.64/5.50      ( ~ v4_tops_1(sK1,sK0)
% 39.64/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_14]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1222,plain,
% 39.64/5.50      ( v4_tops_1(sK1,sK0) != iProver_top
% 39.64/5.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1221]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_17,plain,
% 39.64/5.50      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 39.64/5.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 39.64/5.50      | ~ v2_pre_topc(X0)
% 39.64/5.50      | ~ l1_pre_topc(X0) ),
% 39.64/5.50      inference(cnf_transformation,[],[f78]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1318,plain,
% 39.64/5.50      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0)
% 39.64/5.50      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ v2_pre_topc(sK0)
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_17]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1319,plain,
% 39.64/5.50      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0) = iProver_top
% 39.64/5.50      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | v2_pre_topc(sK0) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_21,plain,
% 39.64/5.50      ( ~ v3_pre_topc(X0,X1)
% 39.64/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ r1_tarski(X0,X2)
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(X1,X2))
% 39.64/5.50      | ~ l1_pre_topc(X1) ),
% 39.64/5.50      inference(cnf_transformation,[],[f82]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1630,plain,
% 39.64/5.50      ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0)
% 39.64/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0)
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_21]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_10521,plain,
% 39.64/5.50      ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0)
% 39.64/5.50      | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_1630]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_10522,plain,
% 39.64/5.50      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_10521]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_155854,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_126111,c_29,c_30,c_31,c_32,c_1124,c_1222,c_1319,
% 39.64/5.50                 c_1334,c_10522]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3017,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_861]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1172,plain,
% 39.64/5.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0)
% 39.64/5.50      | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_18]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3449,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_3017,c_27,c_26,c_1172]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_20,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.64/5.50      | ~ r1_tarski(X0,X2)
% 39.64/5.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 39.64/5.50      | ~ l1_pre_topc(X1) ),
% 39.64/5.50      inference(cnf_transformation,[],[f81]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_859,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.64/5.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.64/5.50      | r1_tarski(X0,X2) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
% 39.64/5.50      | l1_pre_topc(X1) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_5848,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_3449,c_859]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1130,plain,
% 39.64/5.50      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 39.64/5.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1129]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_8291,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_5848,c_30,c_31,c_1130]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_8292,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(renaming,[status(thm)],[c_8291]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_5847,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_3449,c_859]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_8230,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_5847,c_30,c_31,c_1130]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_8231,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
% 39.64/5.50      inference(renaming,[status(thm)],[c_8230]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_0,plain,
% 39.64/5.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 39.64/5.50      inference(cnf_transformation,[],[f62]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_878,plain,
% 39.64/5.50      ( X0 = X1
% 39.64/5.50      | r1_tarski(X0,X1) != iProver_top
% 39.64/5.50      | r1_tarski(X1,X0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_8241,plain,
% 39.64/5.50      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_8231,c_878]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_17476,plain,
% 39.64/5.50      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_8292,c_8241]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2796,plain,
% 39.64/5.50      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 39.64/5.50      | X0 = k1_tops_1(sK0,sK1) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_0]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2797,plain,
% 39.64/5.50      ( X0 = k1_tops_1(sK0,sK1)
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_2796]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_389,plain,( X0 = X0 ),theory(equality) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_3214,plain,
% 39.64/5.50      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_389]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_395,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.64/5.50      theory(equality) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1403,plain,
% 39.64/5.50      ( m1_subset_1(X0,X1)
% 39.64/5.50      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | X0 != k1_tops_1(sK0,sK1)
% 39.64/5.50      | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_395]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_8419,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | X0 != k1_tops_1(sK0,sK1)
% 39.64/5.50      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_1403]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_8421,plain,
% 39.64/5.50      ( X0 != k1_tops_1(sK0,sK1)
% 39.64/5.50      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_8419]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_17538,plain,
% 39.64/5.50      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_17476,c_30,c_31,c_1130,c_2797,c_3214,c_8421]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_155871,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,sK1)
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_155854,c_17538]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_155903,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
% 39.64/5.50      inference(demodulation,[status(thm)],[c_155871,c_42798]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1126,plain,
% 39.64/5.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_11]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1348,plain,
% 39.64/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_20]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2882,plain,
% 39.64/5.50      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 39.64/5.50      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_1348]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_19604,plain,
% 39.64/5.50      ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 39.64/5.50      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_2796]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_156044,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_155903,c_28,c_27,c_26,c_25,c_1123,c_1126,c_1221,
% 39.64/5.50                 c_1318,c_1327,c_2882,c_10521,c_19604]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_12318,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_12314,c_859]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1449,plain,
% 39.64/5.50      ( v3_pre_topc(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
% 39.64/5.50      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ v2_pre_topc(sK0)
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_17]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1450,plain,
% 39.64/5.50      ( v3_pre_topc(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) = iProver_top
% 39.64/5.50      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | v2_pre_topc(sK0) != iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2226,plain,
% 39.64/5.50      ( ~ v3_pre_topc(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
% 39.64/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0))
% 39.64/5.50      | ~ l1_pre_topc(sK0) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_21]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_2232,plain,
% 39.64/5.50      ( v3_pre_topc(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) != iProver_top
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(predicate_to_equality,[status(thm)],[c_2226]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_12360,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top
% 39.64/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_12318,c_30,c_31,c_1133,c_1465]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_12361,plain,
% 39.64/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 39.64/5.50      inference(renaming,[status(thm)],[c_12360]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_156210,plain,
% 39.64/5.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_156044,c_12361]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_163139,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_126362,c_30,c_31,c_1124,c_3000,c_67303,c_156210]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1568,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_870]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1493,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 39.64/5.50      | l1_pre_topc(sK0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_854,c_856]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1227,plain,
% 39.64/5.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.64/5.50      | ~ l1_pre_topc(sK0)
% 39.64/5.50      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_23]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1885,plain,
% 39.64/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_1493,c_27,c_26,c_1227]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1888,plain,
% 39.64/5.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_1568,c_1885]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1892,plain,
% 39.64/5.50      ( r1_xboole_0(X0,k2_tops_1(sK0,sK1)) = iProver_top
% 39.64/5.50      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_1888,c_876]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_163159,plain,
% 39.64/5.50      ( r1_xboole_0(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_163139,c_1892]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_19660,plain,
% 39.64/5.50      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0),k2_tops_1(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_19645,c_1241]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_19979,plain,
% 39.64/5.50      ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_14513,c_19660]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_20380,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0
% 39.64/5.50      | r1_xboole_0(X0,k2_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_19979,c_872]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_24,negated_conjecture,
% 39.64/5.50      ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 39.64/5.50      inference(cnf_transformation,[],[f89]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_390,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1138,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != X0
% 39.64/5.50      | k1_xboole_0 != X0
% 39.64/5.50      | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_390]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1547,plain,
% 39.64/5.50      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
% 39.64/5.50      | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
% 39.64/5.50      | k1_xboole_0 != k1_xboole_0 ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_1138]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_1548,plain,
% 39.64/5.50      ( k1_xboole_0 = k1_xboole_0 ),
% 39.64/5.50      inference(instantiation,[status(thm)],[c_389]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_31765,plain,
% 39.64/5.50      ( r1_xboole_0(X0,k2_tops_1(sK0,sK1)) != iProver_top
% 39.64/5.50      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) != iProver_top ),
% 39.64/5.50      inference(global_propositional_subsumption,
% 39.64/5.50                [status(thm)],
% 39.64/5.50                [c_20380,c_24,c_1547,c_1548]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(c_31773,plain,
% 39.64/5.50      ( r1_xboole_0(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
% 39.64/5.50      inference(superposition,[status(thm)],[c_877,c_31765]) ).
% 39.64/5.50  
% 39.64/5.50  cnf(contradiction,plain,
% 39.64/5.50      ( $false ),
% 39.64/5.50      inference(minisat,[status(thm)],[c_163159,c_31773]) ).
% 39.64/5.50  
% 39.64/5.50  
% 39.64/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.64/5.50  
% 39.64/5.50  ------                               Statistics
% 39.64/5.50  
% 39.64/5.50  ------ Selected
% 39.64/5.50  
% 39.64/5.50  total_time:                             4.872
% 39.64/5.50  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:13:49 EST 2020

% Result     : Theorem 27.78s
% Output     : CNFRefutation 27.78s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 963 expanded)
%              Number of clauses        :  139 ( 414 expanded)
%              Number of leaves         :   22 ( 250 expanded)
%              Depth                    :   19
%              Number of atoms          :  476 (2824 expanded)
%              Number of equality atoms :  175 ( 502 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_365,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X1_43)
    | r1_tarski(k2_xboole_0(X2_43,X0_43),X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_68998,plain,
    ( ~ r1_tarski(X0_43,k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43)))
    | ~ r1_tarski(k1_tops_1(sK0,X3_43),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43)))
    | r1_tarski(k2_xboole_0(X0_43,k1_tops_1(sK0,X3_43)),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43))) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_69734,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43)))
    | ~ r1_tarski(k1_tops_1(sK0,X3_43),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43)))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,X3_43)),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43))) ),
    inference(instantiation,[status(thm)],[c_68998])).

cnf(c_70419,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(X0_43,X1_43)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(X0_43,X1_43)))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(X0_43,X1_43))) ),
    inference(instantiation,[status(thm)],[c_69734])).

cnf(c_93054,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_70419])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_43,X0_43)
    | r1_tarski(k1_tops_1(sK0,X1_43),k1_tops_1(sK0,X0_43)) ),
    inference(subtyping,[status(esa)],[c_200])).

cnf(c_68779,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(X1_43,X2_43),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_43,k2_xboole_0(X1_43,X2_43))
    | r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43))) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_74931,plain,
    ( ~ m1_subset_1(k2_xboole_0(X0_43,X1_43),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(X0_43,X1_43)))
    | ~ r1_tarski(sK2,k2_xboole_0(X0_43,X1_43)) ),
    inference(instantiation,[status(thm)],[c_68779])).

cnf(c_79787,plain,
    ( ~ m1_subset_1(k2_xboole_0(X0_43,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(X0_43,sK2)))
    | ~ r1_tarski(sK2,k2_xboole_0(X0_43,sK2)) ),
    inference(instantiation,[status(thm)],[c_74931])).

cnf(c_79791,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_79787])).

cnf(c_373,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_704,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_43
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_43 ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_731,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(X0_43,X1_43),X2_43)
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0_43,X1_43)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X2_43 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_750,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(X0_43,X1_43),k1_tops_1(sK0,X2_43))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0_43,X1_43)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X2_43) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1362,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(X0_43,X1_43),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0_43,X1_43)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_24570,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0_43))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_56697,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_24570])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_353,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_680,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | k3_subset_1(X1_43,X0_43) = k4_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_670,plain,
    ( k3_subset_1(X0_43,X1_43) = k4_xboole_0(X0_43,X1_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_952,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_680,c_670])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | m1_subset_1(k3_subset_1(X1_43,X0_43),k1_zfmisc_1(X1_43)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_671,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | m1_subset_1(k3_subset_1(X1_43,X0_43),k1_zfmisc_1(X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_1252,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_671])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1523,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1252,c_19])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | k9_subset_1(X1_43,X0_43,X2_43) = k9_subset_1(X1_43,X2_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_669,plain,
    ( k9_subset_1(X0_43,X1_43,X2_43) = k9_subset_1(X0_43,X2_43,X1_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_1540,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_43,k4_xboole_0(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_43) ),
    inference(superposition,[status(thm)],[c_1523,c_669])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_354,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_679,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | k3_subset_1(X1_43,k3_subset_1(X1_43,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_673,plain,
    ( k3_subset_1(X0_43,k3_subset_1(X0_43,X1_43)) = X1_43
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_996,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_679,c_673])).

cnf(c_951,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_679,c_670])).

cnf(c_1000,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_996,c_951])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
    | r1_tarski(k3_subset_1(X1_43,X2_43),k3_subset_1(X1_43,k9_subset_1(X1_43,X2_43,X0_43))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_677,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | m1_subset_1(X2_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(k3_subset_1(X1_43,X2_43),k3_subset_1(X1_43,k9_subset_1(X1_43,X2_43,X0_43))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_2551,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_677])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1203,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_671])).

cnf(c_41641,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2551,c_20,c_1203])).

cnf(c_41650,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_41641])).

cnf(c_1466,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1203,c_20])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
    | k9_subset_1(X1_43,X2_43,k3_subset_1(X1_43,X0_43)) = k7_subset_1(X1_43,X2_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_676,plain,
    ( k9_subset_1(X0_43,X1_43,k3_subset_1(X0_43,X2_43)) = k7_subset_1(X0_43,X1_43,X2_43)
    | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_2353,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_43,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),X0_43,sK1)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_676])).

cnf(c_2361,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_43,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),X0_43,sK1)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2353,c_952])).

cnf(c_5158,plain,
    ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1466,c_2361])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | k7_subset_1(X1_43,X0_43,X2_43) = k4_xboole_0(X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_675,plain,
    ( k7_subset_1(X0_43,X1_43,X2_43) = k4_xboole_0(X1_43,X2_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_1470,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),X0_43) ),
    inference(superposition,[status(thm)],[c_1466,c_675])).

cnf(c_0,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_367,plain,
    ( k4_xboole_0(k4_xboole_0(X0_43,X1_43),X2_43) = k4_xboole_0(X0_43,k2_xboole_0(X1_43,X2_43)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1475,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,X0_43)) ),
    inference(demodulation,[status(thm)],[c_1470,c_367])).

cnf(c_5163,plain,
    ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_5158,c_1475])).

cnf(c_1539,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_43,k4_xboole_0(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43) ),
    inference(superposition,[status(thm)],[c_1466,c_669])).

cnf(c_5713,plain,
    ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_5163,c_1539])).

cnf(c_41665,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41650,c_5713])).

cnf(c_2352,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_43,k3_subset_1(u1_struct_0(sK0),sK2)) = k7_subset_1(u1_struct_0(sK0),X0_43,sK2)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_676])).

cnf(c_2362,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_43,k4_xboole_0(u1_struct_0(sK0),sK2)) = k7_subset_1(u1_struct_0(sK0),X0_43,sK2)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2352,c_951])).

cnf(c_5859,plain,
    ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1523,c_2362])).

cnf(c_5862,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_5859,c_5713])).

cnf(c_1527,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_43) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0_43) ),
    inference(superposition,[status(thm)],[c_1523,c_675])).

cnf(c_1532,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_43) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X0_43)) ),
    inference(demodulation,[status(thm)],[c_1527,c_367])).

cnf(c_5863,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_5862,c_1532])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
    | k4_subset_1(X1_43,X2_43,X0_43) = k2_xboole_0(X2_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_674,plain,
    ( k4_subset_1(X0_43,X1_43,X2_43) = k2_xboole_0(X1_43,X2_43)
    | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_1854,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_43,sK2) = k2_xboole_0(X0_43,sK2)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_674])).

cnf(c_1944,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_680,c_1854])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
    | m1_subset_1(k4_subset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X1_43)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_672,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | m1_subset_1(X2_43,k1_zfmisc_1(X1_43)) != iProver_top
    | m1_subset_1(k4_subset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_2315,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_672])).

cnf(c_10333,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2315,c_19,c_20])).

cnf(c_10362,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_10333,c_673])).

cnf(c_10363,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_10333,c_670])).

cnf(c_10364,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_10362,c_10363])).

cnf(c_41666,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_41665,c_5863,c_10364])).

cnf(c_41676,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_41666])).

cnf(c_4346,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(k1_tops_1(sK0,X2_43),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X3_43,sK2)))
    | X0_43 != k1_tops_1(sK0,X2_43)
    | X1_43 != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X3_43,sK2)) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_11904,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_43),X1_43)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X2_43,sK2)))
    | X1_43 != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X2_43,sK2))
    | k1_tops_1(sK0,X0_43) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4346])).

cnf(c_31346,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k1_tops_1(sK0,X0_43) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_11904])).

cnf(c_31348,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_31346])).

cnf(c_379,plain,
    ( X0_43 != X1_43
    | k1_tops_1(X0_45,X0_43) = k1_tops_1(X0_45,X1_43) ),
    theory(equality)).

cnf(c_1012,plain,
    ( X0_43 != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k1_tops_1(sK0,X0_43) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_10118,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k2_xboole_0(sK1,sK2) != k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_369,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_2488,plain,
    ( k2_xboole_0(X0_43,X1_43) = k2_xboole_0(X0_43,X1_43) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_6614,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2488])).

cnf(c_371,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1165,plain,
    ( X0_43 != X1_43
    | k2_xboole_0(X2_43,X3_43) != X1_43
    | k2_xboole_0(X2_43,X3_43) = X0_43 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_1890,plain,
    ( X0_43 != k2_xboole_0(X1_43,X2_43)
    | k2_xboole_0(X1_43,X2_43) = X0_43
    | k2_xboole_0(X1_43,X2_43) != k2_xboole_0(X1_43,X2_43) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_2671,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_2502,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_43,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_43,k4_subset_1(u1_struct_0(sK0),X1_43,sK2))
    | r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_43,sK2))) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_2504,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_2326,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2315])).

cnf(c_1922,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_43,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_2253,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_1,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_366,plain,
    ( r1_tarski(X0_43,k2_xboole_0(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2002,plain,
    ( r1_tarski(X0_43,k2_xboole_0(X0_43,sK2)) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_2004,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2002])).

cnf(c_800,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,k2_xboole_0(X2_43,X3_43))
    | X0_43 != X2_43
    | X1_43 != k2_xboole_0(X2_43,X3_43) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_882,plain,
    ( r1_tarski(X0_43,k4_subset_1(X1_43,X2_43,X3_43))
    | ~ r1_tarski(X2_43,k2_xboole_0(X2_43,X3_43))
    | X0_43 != X2_43
    | k4_subset_1(X1_43,X2_43,X3_43) != k2_xboole_0(X2_43,X3_43) ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_1325,plain,
    ( r1_tarski(X0_43,k4_subset_1(u1_struct_0(sK0),X1_43,sK2))
    | ~ r1_tarski(X1_43,k2_xboole_0(X1_43,sK2))
    | X0_43 != X1_43
    | k4_subset_1(u1_struct_0(sK0),X1_43,sK2) != k2_xboole_0(X1_43,sK2) ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_1327,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_1264,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0_43,sK2) = k2_xboole_0(X0_43,sK2) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1266,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1264])).

cnf(c_1253,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1252])).

cnf(c_832,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_43
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,X0_43) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_966,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_864,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_805,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_432,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_389,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_387,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93054,c_79791,c_56697,c_41676,c_31348,c_10118,c_6614,c_2671,c_2504,c_2326,c_2253,c_2004,c_1327,c_1266,c_1253,c_966,c_864,c_805,c_432,c_389,c_387,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:18:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.78/3.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.78/3.98  
% 27.78/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.78/3.98  
% 27.78/3.98  ------  iProver source info
% 27.78/3.98  
% 27.78/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.78/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.78/3.98  git: non_committed_changes: false
% 27.78/3.98  git: last_make_outside_of_git: false
% 27.78/3.98  
% 27.78/3.98  ------ 
% 27.78/3.98  
% 27.78/3.98  ------ Input Options
% 27.78/3.98  
% 27.78/3.98  --out_options                           all
% 27.78/3.98  --tptp_safe_out                         true
% 27.78/3.98  --problem_path                          ""
% 27.78/3.98  --include_path                          ""
% 27.78/3.98  --clausifier                            res/vclausify_rel
% 27.78/3.98  --clausifier_options                    ""
% 27.78/3.98  --stdin                                 false
% 27.78/3.98  --stats_out                             all
% 27.78/3.98  
% 27.78/3.98  ------ General Options
% 27.78/3.98  
% 27.78/3.98  --fof                                   false
% 27.78/3.98  --time_out_real                         305.
% 27.78/3.98  --time_out_virtual                      -1.
% 27.78/3.98  --symbol_type_check                     false
% 27.78/3.98  --clausify_out                          false
% 27.78/3.98  --sig_cnt_out                           false
% 27.78/3.98  --trig_cnt_out                          false
% 27.78/3.98  --trig_cnt_out_tolerance                1.
% 27.78/3.98  --trig_cnt_out_sk_spl                   false
% 27.78/3.98  --abstr_cl_out                          false
% 27.78/3.98  
% 27.78/3.98  ------ Global Options
% 27.78/3.98  
% 27.78/3.98  --schedule                              default
% 27.78/3.98  --add_important_lit                     false
% 27.78/3.98  --prop_solver_per_cl                    1000
% 27.78/3.98  --min_unsat_core                        false
% 27.78/3.98  --soft_assumptions                      false
% 27.78/3.98  --soft_lemma_size                       3
% 27.78/3.98  --prop_impl_unit_size                   0
% 27.78/3.98  --prop_impl_unit                        []
% 27.78/3.98  --share_sel_clauses                     true
% 27.78/3.98  --reset_solvers                         false
% 27.78/3.98  --bc_imp_inh                            [conj_cone]
% 27.78/3.98  --conj_cone_tolerance                   3.
% 27.78/3.98  --extra_neg_conj                        none
% 27.78/3.98  --large_theory_mode                     true
% 27.78/3.98  --prolific_symb_bound                   200
% 27.78/3.98  --lt_threshold                          2000
% 27.78/3.98  --clause_weak_htbl                      true
% 27.78/3.98  --gc_record_bc_elim                     false
% 27.78/3.98  
% 27.78/3.98  ------ Preprocessing Options
% 27.78/3.98  
% 27.78/3.98  --preprocessing_flag                    true
% 27.78/3.98  --time_out_prep_mult                    0.1
% 27.78/3.98  --splitting_mode                        input
% 27.78/3.98  --splitting_grd                         true
% 27.78/3.98  --splitting_cvd                         false
% 27.78/3.98  --splitting_cvd_svl                     false
% 27.78/3.98  --splitting_nvd                         32
% 27.78/3.98  --sub_typing                            true
% 27.78/3.98  --prep_gs_sim                           true
% 27.78/3.98  --prep_unflatten                        true
% 27.78/3.98  --prep_res_sim                          true
% 27.78/3.98  --prep_upred                            true
% 27.78/3.98  --prep_sem_filter                       exhaustive
% 27.78/3.98  --prep_sem_filter_out                   false
% 27.78/3.98  --pred_elim                             true
% 27.78/3.98  --res_sim_input                         true
% 27.78/3.98  --eq_ax_congr_red                       true
% 27.78/3.98  --pure_diseq_elim                       true
% 27.78/3.98  --brand_transform                       false
% 27.78/3.98  --non_eq_to_eq                          false
% 27.78/3.98  --prep_def_merge                        true
% 27.78/3.98  --prep_def_merge_prop_impl              false
% 27.78/3.98  --prep_def_merge_mbd                    true
% 27.78/3.98  --prep_def_merge_tr_red                 false
% 27.78/3.98  --prep_def_merge_tr_cl                  false
% 27.78/3.98  --smt_preprocessing                     true
% 27.78/3.98  --smt_ac_axioms                         fast
% 27.78/3.98  --preprocessed_out                      false
% 27.78/3.98  --preprocessed_stats                    false
% 27.78/3.98  
% 27.78/3.98  ------ Abstraction refinement Options
% 27.78/3.98  
% 27.78/3.98  --abstr_ref                             []
% 27.78/3.98  --abstr_ref_prep                        false
% 27.78/3.98  --abstr_ref_until_sat                   false
% 27.78/3.98  --abstr_ref_sig_restrict                funpre
% 27.78/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.78/3.98  --abstr_ref_under                       []
% 27.78/3.98  
% 27.78/3.98  ------ SAT Options
% 27.78/3.98  
% 27.78/3.98  --sat_mode                              false
% 27.78/3.98  --sat_fm_restart_options                ""
% 27.78/3.98  --sat_gr_def                            false
% 27.78/3.98  --sat_epr_types                         true
% 27.78/3.98  --sat_non_cyclic_types                  false
% 27.78/3.98  --sat_finite_models                     false
% 27.78/3.98  --sat_fm_lemmas                         false
% 27.78/3.98  --sat_fm_prep                           false
% 27.78/3.98  --sat_fm_uc_incr                        true
% 27.78/3.98  --sat_out_model                         small
% 27.78/3.98  --sat_out_clauses                       false
% 27.78/3.98  
% 27.78/3.98  ------ QBF Options
% 27.78/3.98  
% 27.78/3.98  --qbf_mode                              false
% 27.78/3.98  --qbf_elim_univ                         false
% 27.78/3.98  --qbf_dom_inst                          none
% 27.78/3.98  --qbf_dom_pre_inst                      false
% 27.78/3.98  --qbf_sk_in                             false
% 27.78/3.98  --qbf_pred_elim                         true
% 27.78/3.98  --qbf_split                             512
% 27.78/3.98  
% 27.78/3.98  ------ BMC1 Options
% 27.78/3.98  
% 27.78/3.98  --bmc1_incremental                      false
% 27.78/3.98  --bmc1_axioms                           reachable_all
% 27.78/3.98  --bmc1_min_bound                        0
% 27.78/3.98  --bmc1_max_bound                        -1
% 27.78/3.98  --bmc1_max_bound_default                -1
% 27.78/3.98  --bmc1_symbol_reachability              true
% 27.78/3.98  --bmc1_property_lemmas                  false
% 27.78/3.98  --bmc1_k_induction                      false
% 27.78/3.98  --bmc1_non_equiv_states                 false
% 27.78/3.98  --bmc1_deadlock                         false
% 27.78/3.98  --bmc1_ucm                              false
% 27.78/3.98  --bmc1_add_unsat_core                   none
% 27.78/3.98  --bmc1_unsat_core_children              false
% 27.78/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.78/3.98  --bmc1_out_stat                         full
% 27.78/3.98  --bmc1_ground_init                      false
% 27.78/3.98  --bmc1_pre_inst_next_state              false
% 27.78/3.98  --bmc1_pre_inst_state                   false
% 27.78/3.98  --bmc1_pre_inst_reach_state             false
% 27.78/3.98  --bmc1_out_unsat_core                   false
% 27.78/3.98  --bmc1_aig_witness_out                  false
% 27.78/3.98  --bmc1_verbose                          false
% 27.78/3.98  --bmc1_dump_clauses_tptp                false
% 27.78/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.78/3.98  --bmc1_dump_file                        -
% 27.78/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.78/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.78/3.98  --bmc1_ucm_extend_mode                  1
% 27.78/3.98  --bmc1_ucm_init_mode                    2
% 27.78/3.98  --bmc1_ucm_cone_mode                    none
% 27.78/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.78/3.98  --bmc1_ucm_relax_model                  4
% 27.78/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.78/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.78/3.98  --bmc1_ucm_layered_model                none
% 27.78/3.98  --bmc1_ucm_max_lemma_size               10
% 27.78/3.98  
% 27.78/3.98  ------ AIG Options
% 27.78/3.98  
% 27.78/3.98  --aig_mode                              false
% 27.78/3.98  
% 27.78/3.98  ------ Instantiation Options
% 27.78/3.98  
% 27.78/3.98  --instantiation_flag                    true
% 27.78/3.98  --inst_sos_flag                         true
% 27.78/3.98  --inst_sos_phase                        true
% 27.78/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.78/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.78/3.98  --inst_lit_sel_side                     num_symb
% 27.78/3.98  --inst_solver_per_active                1400
% 27.78/3.98  --inst_solver_calls_frac                1.
% 27.78/3.98  --inst_passive_queue_type               priority_queues
% 27.78/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.78/3.98  --inst_passive_queues_freq              [25;2]
% 27.78/3.98  --inst_dismatching                      true
% 27.78/3.98  --inst_eager_unprocessed_to_passive     true
% 27.78/3.98  --inst_prop_sim_given                   true
% 27.78/3.98  --inst_prop_sim_new                     false
% 27.78/3.98  --inst_subs_new                         false
% 27.78/3.98  --inst_eq_res_simp                      false
% 27.78/3.98  --inst_subs_given                       false
% 27.78/3.98  --inst_orphan_elimination               true
% 27.78/3.98  --inst_learning_loop_flag               true
% 27.78/3.98  --inst_learning_start                   3000
% 27.78/3.98  --inst_learning_factor                  2
% 27.78/3.98  --inst_start_prop_sim_after_learn       3
% 27.78/3.98  --inst_sel_renew                        solver
% 27.78/3.98  --inst_lit_activity_flag                true
% 27.78/3.98  --inst_restr_to_given                   false
% 27.78/3.98  --inst_activity_threshold               500
% 27.78/3.98  --inst_out_proof                        true
% 27.78/3.98  
% 27.78/3.98  ------ Resolution Options
% 27.78/3.98  
% 27.78/3.98  --resolution_flag                       true
% 27.78/3.98  --res_lit_sel                           adaptive
% 27.78/3.98  --res_lit_sel_side                      none
% 27.78/3.98  --res_ordering                          kbo
% 27.78/3.98  --res_to_prop_solver                    active
% 27.78/3.98  --res_prop_simpl_new                    false
% 27.78/3.98  --res_prop_simpl_given                  true
% 27.78/3.98  --res_passive_queue_type                priority_queues
% 27.78/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.78/3.98  --res_passive_queues_freq               [15;5]
% 27.78/3.98  --res_forward_subs                      full
% 27.78/3.98  --res_backward_subs                     full
% 27.78/3.98  --res_forward_subs_resolution           true
% 27.78/3.98  --res_backward_subs_resolution          true
% 27.78/3.98  --res_orphan_elimination                true
% 27.78/3.98  --res_time_limit                        2.
% 27.78/3.98  --res_out_proof                         true
% 27.78/3.98  
% 27.78/3.98  ------ Superposition Options
% 27.78/3.98  
% 27.78/3.98  --superposition_flag                    true
% 27.78/3.98  --sup_passive_queue_type                priority_queues
% 27.78/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.78/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.78/3.98  --demod_completeness_check              fast
% 27.78/3.98  --demod_use_ground                      true
% 27.78/3.98  --sup_to_prop_solver                    passive
% 27.78/3.98  --sup_prop_simpl_new                    true
% 27.78/3.98  --sup_prop_simpl_given                  true
% 27.78/3.98  --sup_fun_splitting                     true
% 27.78/3.98  --sup_smt_interval                      50000
% 27.78/3.98  
% 27.78/3.98  ------ Superposition Simplification Setup
% 27.78/3.98  
% 27.78/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.78/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.78/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.78/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.78/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.78/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.78/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.78/3.98  --sup_immed_triv                        [TrivRules]
% 27.78/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.78/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.78/3.98  --sup_immed_bw_main                     []
% 27.78/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.78/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.78/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.78/3.98  --sup_input_bw                          []
% 27.78/3.98  
% 27.78/3.98  ------ Combination Options
% 27.78/3.98  
% 27.78/3.98  --comb_res_mult                         3
% 27.78/3.98  --comb_sup_mult                         2
% 27.78/3.98  --comb_inst_mult                        10
% 27.78/3.98  
% 27.78/3.98  ------ Debug Options
% 27.78/3.98  
% 27.78/3.98  --dbg_backtrace                         false
% 27.78/3.98  --dbg_dump_prop_clauses                 false
% 27.78/3.98  --dbg_dump_prop_clauses_file            -
% 27.78/3.98  --dbg_out_stat                          false
% 27.78/3.98  ------ Parsing...
% 27.78/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.78/3.98  
% 27.78/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.78/3.98  
% 27.78/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.78/3.98  
% 27.78/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.78/3.98  ------ Proving...
% 27.78/3.98  ------ Problem Properties 
% 27.78/3.98  
% 27.78/3.98  
% 27.78/3.98  clauses                                 17
% 27.78/3.98  conjectures                             3
% 27.78/3.98  EPR                                     0
% 27.78/3.98  Horn                                    17
% 27.78/3.98  unary                                   5
% 27.78/3.98  binary                                  6
% 27.78/3.98  lits                                    36
% 27.78/3.98  lits eq                                 7
% 27.78/3.98  fd_pure                                 0
% 27.78/3.98  fd_pseudo                               0
% 27.78/3.98  fd_cond                                 0
% 27.78/3.98  fd_pseudo_cond                          0
% 27.78/3.98  AC symbols                              0
% 27.78/3.98  
% 27.78/3.98  ------ Schedule dynamic 5 is on 
% 27.78/3.98  
% 27.78/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.78/3.98  
% 27.78/3.98  
% 27.78/3.98  ------ 
% 27.78/3.98  Current options:
% 27.78/3.98  ------ 
% 27.78/3.98  
% 27.78/3.98  ------ Input Options
% 27.78/3.98  
% 27.78/3.98  --out_options                           all
% 27.78/3.98  --tptp_safe_out                         true
% 27.78/3.98  --problem_path                          ""
% 27.78/3.98  --include_path                          ""
% 27.78/3.98  --clausifier                            res/vclausify_rel
% 27.78/3.98  --clausifier_options                    ""
% 27.78/3.98  --stdin                                 false
% 27.78/3.98  --stats_out                             all
% 27.78/3.98  
% 27.78/3.98  ------ General Options
% 27.78/3.98  
% 27.78/3.98  --fof                                   false
% 27.78/3.98  --time_out_real                         305.
% 27.78/3.98  --time_out_virtual                      -1.
% 27.78/3.98  --symbol_type_check                     false
% 27.78/3.98  --clausify_out                          false
% 27.78/3.98  --sig_cnt_out                           false
% 27.78/3.98  --trig_cnt_out                          false
% 27.78/3.98  --trig_cnt_out_tolerance                1.
% 27.78/3.98  --trig_cnt_out_sk_spl                   false
% 27.78/3.98  --abstr_cl_out                          false
% 27.78/3.98  
% 27.78/3.98  ------ Global Options
% 27.78/3.98  
% 27.78/3.98  --schedule                              default
% 27.78/3.98  --add_important_lit                     false
% 27.78/3.98  --prop_solver_per_cl                    1000
% 27.78/3.98  --min_unsat_core                        false
% 27.78/3.98  --soft_assumptions                      false
% 27.78/3.98  --soft_lemma_size                       3
% 27.78/3.98  --prop_impl_unit_size                   0
% 27.78/3.98  --prop_impl_unit                        []
% 27.78/3.98  --share_sel_clauses                     true
% 27.78/3.98  --reset_solvers                         false
% 27.78/3.98  --bc_imp_inh                            [conj_cone]
% 27.78/3.98  --conj_cone_tolerance                   3.
% 27.78/3.98  --extra_neg_conj                        none
% 27.78/3.98  --large_theory_mode                     true
% 27.78/3.98  --prolific_symb_bound                   200
% 27.78/3.98  --lt_threshold                          2000
% 27.78/3.98  --clause_weak_htbl                      true
% 27.78/3.98  --gc_record_bc_elim                     false
% 27.78/3.98  
% 27.78/3.98  ------ Preprocessing Options
% 27.78/3.98  
% 27.78/3.98  --preprocessing_flag                    true
% 27.78/3.98  --time_out_prep_mult                    0.1
% 27.78/3.98  --splitting_mode                        input
% 27.78/3.98  --splitting_grd                         true
% 27.78/3.98  --splitting_cvd                         false
% 27.78/3.98  --splitting_cvd_svl                     false
% 27.78/3.98  --splitting_nvd                         32
% 27.78/3.98  --sub_typing                            true
% 27.78/3.98  --prep_gs_sim                           true
% 27.78/3.98  --prep_unflatten                        true
% 27.78/3.98  --prep_res_sim                          true
% 27.78/3.98  --prep_upred                            true
% 27.78/3.98  --prep_sem_filter                       exhaustive
% 27.78/3.98  --prep_sem_filter_out                   false
% 27.78/3.98  --pred_elim                             true
% 27.78/3.98  --res_sim_input                         true
% 27.78/3.98  --eq_ax_congr_red                       true
% 27.78/3.98  --pure_diseq_elim                       true
% 27.78/3.98  --brand_transform                       false
% 27.78/3.98  --non_eq_to_eq                          false
% 27.78/3.98  --prep_def_merge                        true
% 27.78/3.98  --prep_def_merge_prop_impl              false
% 27.78/3.98  --prep_def_merge_mbd                    true
% 27.78/3.98  --prep_def_merge_tr_red                 false
% 27.78/3.98  --prep_def_merge_tr_cl                  false
% 27.78/3.98  --smt_preprocessing                     true
% 27.78/3.98  --smt_ac_axioms                         fast
% 27.78/3.98  --preprocessed_out                      false
% 27.78/3.98  --preprocessed_stats                    false
% 27.78/3.98  
% 27.78/3.98  ------ Abstraction refinement Options
% 27.78/3.98  
% 27.78/3.98  --abstr_ref                             []
% 27.78/3.98  --abstr_ref_prep                        false
% 27.78/3.98  --abstr_ref_until_sat                   false
% 27.78/3.98  --abstr_ref_sig_restrict                funpre
% 27.78/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.78/3.98  --abstr_ref_under                       []
% 27.78/3.98  
% 27.78/3.98  ------ SAT Options
% 27.78/3.98  
% 27.78/3.98  --sat_mode                              false
% 27.78/3.98  --sat_fm_restart_options                ""
% 27.78/3.98  --sat_gr_def                            false
% 27.78/3.98  --sat_epr_types                         true
% 27.78/3.98  --sat_non_cyclic_types                  false
% 27.78/3.98  --sat_finite_models                     false
% 27.78/3.98  --sat_fm_lemmas                         false
% 27.78/3.98  --sat_fm_prep                           false
% 27.78/3.98  --sat_fm_uc_incr                        true
% 27.78/3.98  --sat_out_model                         small
% 27.78/3.98  --sat_out_clauses                       false
% 27.78/3.98  
% 27.78/3.98  ------ QBF Options
% 27.78/3.98  
% 27.78/3.98  --qbf_mode                              false
% 27.78/3.98  --qbf_elim_univ                         false
% 27.78/3.98  --qbf_dom_inst                          none
% 27.78/3.98  --qbf_dom_pre_inst                      false
% 27.78/3.98  --qbf_sk_in                             false
% 27.78/3.98  --qbf_pred_elim                         true
% 27.78/3.98  --qbf_split                             512
% 27.78/3.98  
% 27.78/3.98  ------ BMC1 Options
% 27.78/3.98  
% 27.78/3.98  --bmc1_incremental                      false
% 27.78/3.98  --bmc1_axioms                           reachable_all
% 27.78/3.98  --bmc1_min_bound                        0
% 27.78/3.98  --bmc1_max_bound                        -1
% 27.78/3.98  --bmc1_max_bound_default                -1
% 27.78/3.98  --bmc1_symbol_reachability              true
% 27.78/3.98  --bmc1_property_lemmas                  false
% 27.78/3.98  --bmc1_k_induction                      false
% 27.78/3.98  --bmc1_non_equiv_states                 false
% 27.78/3.98  --bmc1_deadlock                         false
% 27.78/3.98  --bmc1_ucm                              false
% 27.78/3.98  --bmc1_add_unsat_core                   none
% 27.78/3.98  --bmc1_unsat_core_children              false
% 27.78/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.78/3.98  --bmc1_out_stat                         full
% 27.78/3.98  --bmc1_ground_init                      false
% 27.78/3.98  --bmc1_pre_inst_next_state              false
% 27.78/3.98  --bmc1_pre_inst_state                   false
% 27.78/3.98  --bmc1_pre_inst_reach_state             false
% 27.78/3.98  --bmc1_out_unsat_core                   false
% 27.78/3.98  --bmc1_aig_witness_out                  false
% 27.78/3.98  --bmc1_verbose                          false
% 27.78/3.98  --bmc1_dump_clauses_tptp                false
% 27.78/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.78/3.98  --bmc1_dump_file                        -
% 27.78/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.78/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.78/3.98  --bmc1_ucm_extend_mode                  1
% 27.78/3.98  --bmc1_ucm_init_mode                    2
% 27.78/3.98  --bmc1_ucm_cone_mode                    none
% 27.78/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.78/3.98  --bmc1_ucm_relax_model                  4
% 27.78/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.78/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.78/3.98  --bmc1_ucm_layered_model                none
% 27.78/3.98  --bmc1_ucm_max_lemma_size               10
% 27.78/3.98  
% 27.78/3.98  ------ AIG Options
% 27.78/3.98  
% 27.78/3.98  --aig_mode                              false
% 27.78/3.98  
% 27.78/3.98  ------ Instantiation Options
% 27.78/3.98  
% 27.78/3.98  --instantiation_flag                    true
% 27.78/3.98  --inst_sos_flag                         true
% 27.78/3.98  --inst_sos_phase                        true
% 27.78/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.78/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.78/3.98  --inst_lit_sel_side                     none
% 27.78/3.98  --inst_solver_per_active                1400
% 27.78/3.98  --inst_solver_calls_frac                1.
% 27.78/3.98  --inst_passive_queue_type               priority_queues
% 27.78/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.78/3.98  --inst_passive_queues_freq              [25;2]
% 27.78/3.98  --inst_dismatching                      true
% 27.78/3.98  --inst_eager_unprocessed_to_passive     true
% 27.78/3.98  --inst_prop_sim_given                   true
% 27.78/3.98  --inst_prop_sim_new                     false
% 27.78/3.98  --inst_subs_new                         false
% 27.78/3.98  --inst_eq_res_simp                      false
% 27.78/3.98  --inst_subs_given                       false
% 27.78/3.98  --inst_orphan_elimination               true
% 27.78/3.98  --inst_learning_loop_flag               true
% 27.78/3.98  --inst_learning_start                   3000
% 27.78/3.98  --inst_learning_factor                  2
% 27.78/3.98  --inst_start_prop_sim_after_learn       3
% 27.78/3.98  --inst_sel_renew                        solver
% 27.78/3.98  --inst_lit_activity_flag                true
% 27.78/3.98  --inst_restr_to_given                   false
% 27.78/3.98  --inst_activity_threshold               500
% 27.78/3.98  --inst_out_proof                        true
% 27.78/3.98  
% 27.78/3.98  ------ Resolution Options
% 27.78/3.98  
% 27.78/3.98  --resolution_flag                       false
% 27.78/3.98  --res_lit_sel                           adaptive
% 27.78/3.98  --res_lit_sel_side                      none
% 27.78/3.98  --res_ordering                          kbo
% 27.78/3.98  --res_to_prop_solver                    active
% 27.78/3.98  --res_prop_simpl_new                    false
% 27.78/3.98  --res_prop_simpl_given                  true
% 27.78/3.98  --res_passive_queue_type                priority_queues
% 27.78/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.78/3.98  --res_passive_queues_freq               [15;5]
% 27.78/3.98  --res_forward_subs                      full
% 27.78/3.98  --res_backward_subs                     full
% 27.78/3.98  --res_forward_subs_resolution           true
% 27.78/3.98  --res_backward_subs_resolution          true
% 27.78/3.98  --res_orphan_elimination                true
% 27.78/3.98  --res_time_limit                        2.
% 27.78/3.98  --res_out_proof                         true
% 27.78/3.98  
% 27.78/3.98  ------ Superposition Options
% 27.78/3.98  
% 27.78/3.98  --superposition_flag                    true
% 27.78/3.98  --sup_passive_queue_type                priority_queues
% 27.78/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.78/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.78/3.98  --demod_completeness_check              fast
% 27.78/3.98  --demod_use_ground                      true
% 27.78/3.98  --sup_to_prop_solver                    passive
% 27.78/3.98  --sup_prop_simpl_new                    true
% 27.78/3.98  --sup_prop_simpl_given                  true
% 27.78/3.98  --sup_fun_splitting                     true
% 27.78/3.98  --sup_smt_interval                      50000
% 27.78/3.98  
% 27.78/3.98  ------ Superposition Simplification Setup
% 27.78/3.98  
% 27.78/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.78/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.78/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.78/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.78/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.78/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.78/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.78/3.98  --sup_immed_triv                        [TrivRules]
% 27.78/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.78/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.78/3.98  --sup_immed_bw_main                     []
% 27.78/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.78/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.78/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.78/3.98  --sup_input_bw                          []
% 27.78/3.98  
% 27.78/3.98  ------ Combination Options
% 27.78/3.98  
% 27.78/3.98  --comb_res_mult                         3
% 27.78/3.98  --comb_sup_mult                         2
% 27.78/3.98  --comb_inst_mult                        10
% 27.78/3.98  
% 27.78/3.98  ------ Debug Options
% 27.78/3.98  
% 27.78/3.98  --dbg_backtrace                         false
% 27.78/3.98  --dbg_dump_prop_clauses                 false
% 27.78/3.98  --dbg_dump_prop_clauses_file            -
% 27.78/3.98  --dbg_out_stat                          false
% 27.78/3.98  
% 27.78/3.98  
% 27.78/3.98  
% 27.78/3.98  
% 27.78/3.98  ------ Proving...
% 27.78/3.98  
% 27.78/3.98  
% 27.78/3.98  % SZS status Theorem for theBenchmark.p
% 27.78/3.98  
% 27.78/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.78/3.98  
% 27.78/3.98  fof(f3,axiom,(
% 27.78/3.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f17,plain,(
% 27.78/3.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 27.78/3.98    inference(ennf_transformation,[],[f3])).
% 27.78/3.98  
% 27.78/3.98  fof(f18,plain,(
% 27.78/3.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 27.78/3.98    inference(flattening,[],[f17])).
% 27.78/3.98  
% 27.78/3.98  fof(f41,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 27.78/3.98    inference(cnf_transformation,[],[f18])).
% 27.78/3.98  
% 27.78/3.98  fof(f14,axiom,(
% 27.78/3.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f32,plain,(
% 27.78/3.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.78/3.98    inference(ennf_transformation,[],[f14])).
% 27.78/3.98  
% 27.78/3.98  fof(f33,plain,(
% 27.78/3.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.78/3.98    inference(flattening,[],[f32])).
% 27.78/3.98  
% 27.78/3.98  fof(f52,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.78/3.98    inference(cnf_transformation,[],[f33])).
% 27.78/3.98  
% 27.78/3.98  fof(f15,conjecture,(
% 27.78/3.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f16,negated_conjecture,(
% 27.78/3.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 27.78/3.98    inference(negated_conjecture,[],[f15])).
% 27.78/3.98  
% 27.78/3.98  fof(f34,plain,(
% 27.78/3.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.78/3.98    inference(ennf_transformation,[],[f16])).
% 27.78/3.98  
% 27.78/3.98  fof(f37,plain,(
% 27.78/3.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.78/3.98    introduced(choice_axiom,[])).
% 27.78/3.98  
% 27.78/3.98  fof(f36,plain,(
% 27.78/3.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.78/3.98    introduced(choice_axiom,[])).
% 27.78/3.98  
% 27.78/3.98  fof(f35,plain,(
% 27.78/3.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 27.78/3.98    introduced(choice_axiom,[])).
% 27.78/3.98  
% 27.78/3.98  fof(f38,plain,(
% 27.78/3.98    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 27.78/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).
% 27.78/3.98  
% 27.78/3.98  fof(f53,plain,(
% 27.78/3.98    l1_pre_topc(sK0)),
% 27.78/3.98    inference(cnf_transformation,[],[f38])).
% 27.78/3.98  
% 27.78/3.98  fof(f54,plain,(
% 27.78/3.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.78/3.98    inference(cnf_transformation,[],[f38])).
% 27.78/3.98  
% 27.78/3.98  fof(f5,axiom,(
% 27.78/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f20,plain,(
% 27.78/3.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(ennf_transformation,[],[f5])).
% 27.78/3.98  
% 27.78/3.98  fof(f43,plain,(
% 27.78/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f20])).
% 27.78/3.98  
% 27.78/3.98  fof(f6,axiom,(
% 27.78/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f21,plain,(
% 27.78/3.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(ennf_transformation,[],[f6])).
% 27.78/3.98  
% 27.78/3.98  fof(f44,plain,(
% 27.78/3.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f21])).
% 27.78/3.98  
% 27.78/3.98  fof(f4,axiom,(
% 27.78/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f19,plain,(
% 27.78/3.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(ennf_transformation,[],[f4])).
% 27.78/3.98  
% 27.78/3.98  fof(f42,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f19])).
% 27.78/3.98  
% 27.78/3.98  fof(f55,plain,(
% 27.78/3.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.78/3.98    inference(cnf_transformation,[],[f38])).
% 27.78/3.98  
% 27.78/3.98  fof(f8,axiom,(
% 27.78/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f24,plain,(
% 27.78/3.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(ennf_transformation,[],[f8])).
% 27.78/3.98  
% 27.78/3.98  fof(f46,plain,(
% 27.78/3.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f24])).
% 27.78/3.98  
% 27.78/3.98  fof(f12,axiom,(
% 27.78/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f29,plain,(
% 27.78/3.98    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(ennf_transformation,[],[f12])).
% 27.78/3.98  
% 27.78/3.98  fof(f50,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f29])).
% 27.78/3.98  
% 27.78/3.98  fof(f11,axiom,(
% 27.78/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f28,plain,(
% 27.78/3.98    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(ennf_transformation,[],[f11])).
% 27.78/3.98  
% 27.78/3.98  fof(f49,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f28])).
% 27.78/3.98  
% 27.78/3.98  fof(f10,axiom,(
% 27.78/3.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f27,plain,(
% 27.78/3.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(ennf_transformation,[],[f10])).
% 27.78/3.98  
% 27.78/3.98  fof(f48,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f27])).
% 27.78/3.98  
% 27.78/3.98  fof(f1,axiom,(
% 27.78/3.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f39,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 27.78/3.98    inference(cnf_transformation,[],[f1])).
% 27.78/3.98  
% 27.78/3.98  fof(f9,axiom,(
% 27.78/3.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f25,plain,(
% 27.78/3.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.78/3.98    inference(ennf_transformation,[],[f9])).
% 27.78/3.98  
% 27.78/3.98  fof(f26,plain,(
% 27.78/3.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(flattening,[],[f25])).
% 27.78/3.98  
% 27.78/3.98  fof(f47,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f26])).
% 27.78/3.98  
% 27.78/3.98  fof(f7,axiom,(
% 27.78/3.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f22,plain,(
% 27.78/3.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.78/3.98    inference(ennf_transformation,[],[f7])).
% 27.78/3.98  
% 27.78/3.98  fof(f23,plain,(
% 27.78/3.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.78/3.98    inference(flattening,[],[f22])).
% 27.78/3.98  
% 27.78/3.98  fof(f45,plain,(
% 27.78/3.98    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f23])).
% 27.78/3.98  
% 27.78/3.98  fof(f2,axiom,(
% 27.78/3.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f40,plain,(
% 27.78/3.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.78/3.98    inference(cnf_transformation,[],[f2])).
% 27.78/3.98  
% 27.78/3.98  fof(f13,axiom,(
% 27.78/3.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 27.78/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.78/3.98  
% 27.78/3.98  fof(f30,plain,(
% 27.78/3.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.78/3.98    inference(ennf_transformation,[],[f13])).
% 27.78/3.98  
% 27.78/3.98  fof(f31,plain,(
% 27.78/3.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.78/3.98    inference(flattening,[],[f30])).
% 27.78/3.98  
% 27.78/3.98  fof(f51,plain,(
% 27.78/3.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.78/3.98    inference(cnf_transformation,[],[f31])).
% 27.78/3.98  
% 27.78/3.98  fof(f56,plain,(
% 27.78/3.98    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 27.78/3.98    inference(cnf_transformation,[],[f38])).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2,plain,
% 27.78/3.98      ( ~ r1_tarski(X0,X1)
% 27.78/3.98      | ~ r1_tarski(X2,X1)
% 27.78/3.98      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 27.78/3.98      inference(cnf_transformation,[],[f41]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_365,plain,
% 27.78/3.98      ( ~ r1_tarski(X0_43,X1_43)
% 27.78/3.98      | ~ r1_tarski(X2_43,X1_43)
% 27.78/3.98      | r1_tarski(k2_xboole_0(X2_43,X0_43),X1_43) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_2]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_68998,plain,
% 27.78/3.98      ( ~ r1_tarski(X0_43,k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43)))
% 27.78/3.98      | ~ r1_tarski(k1_tops_1(sK0,X3_43),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43)))
% 27.78/3.98      | r1_tarski(k2_xboole_0(X0_43,k1_tops_1(sK0,X3_43)),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43))) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_365]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_69734,plain,
% 27.78/3.98      ( ~ r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43)))
% 27.78/3.98      | ~ r1_tarski(k1_tops_1(sK0,X3_43),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43)))
% 27.78/3.98      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,X3_43)),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43))) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_68998]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_70419,plain,
% 27.78/3.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(X0_43,X1_43)))
% 27.78/3.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(X0_43,X1_43)))
% 27.78/3.98      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(X0_43,X1_43))) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_69734]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_93054,plain,
% 27.78/3.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.78/3.98      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_70419]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_13,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.78/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.78/3.98      | ~ r1_tarski(X0,X2)
% 27.78/3.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.78/3.98      | ~ l1_pre_topc(X1) ),
% 27.78/3.98      inference(cnf_transformation,[],[f52]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_17,negated_conjecture,
% 27.78/3.98      ( l1_pre_topc(sK0) ),
% 27.78/3.98      inference(cnf_transformation,[],[f53]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_199,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.78/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.78/3.98      | ~ r1_tarski(X0,X2)
% 27.78/3.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.78/3.98      | sK0 != X1 ),
% 27.78/3.98      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_200,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ r1_tarski(X1,X0)
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 27.78/3.98      inference(unflattening,[status(thm)],[c_199]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_352,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ r1_tarski(X1_43,X0_43)
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,X1_43),k1_tops_1(sK0,X0_43)) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_200]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_68779,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(k2_xboole_0(X1_43,X2_43),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ r1_tarski(X0_43,k2_xboole_0(X1_43,X2_43))
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,k2_xboole_0(X1_43,X2_43))) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_352]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_74931,plain,
% 27.78/3.98      ( ~ m1_subset_1(k2_xboole_0(X0_43,X1_43),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(X0_43,X1_43)))
% 27.78/3.98      | ~ r1_tarski(sK2,k2_xboole_0(X0_43,X1_43)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_68779]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_79787,plain,
% 27.78/3.98      ( ~ m1_subset_1(k2_xboole_0(X0_43,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(X0_43,sK2)))
% 27.78/3.98      | ~ r1_tarski(sK2,k2_xboole_0(X0_43,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_74931]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_79791,plain,
% 27.78/3.98      ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_79787]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_373,plain,
% 27.78/3.98      ( ~ r1_tarski(X0_43,X1_43)
% 27.78/3.98      | r1_tarski(X2_43,X3_43)
% 27.78/3.98      | X2_43 != X0_43
% 27.78/3.98      | X3_43 != X1_43 ),
% 27.78/3.98      theory(equality) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_704,plain,
% 27.78/3.98      ( ~ r1_tarski(X0_43,X1_43)
% 27.78/3.98      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_43
% 27.78/3.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_43 ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_373]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_731,plain,
% 27.78/3.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(k2_xboole_0(X0_43,X1_43),X2_43)
% 27.78/3.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0_43,X1_43)
% 27.78/3.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X2_43 ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_704]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_750,plain,
% 27.78/3.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(k2_xboole_0(X0_43,X1_43),k1_tops_1(sK0,X2_43))
% 27.78/3.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0_43,X1_43)
% 27.78/3.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X2_43) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_731]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1362,plain,
% 27.78/3.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(k2_xboole_0(X0_43,X1_43),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.78/3.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0_43,X1_43)
% 27.78/3.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_750]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_24570,plain,
% 27.78/3.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.78/3.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0_43))
% 27.78/3.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_1362]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_56697,plain,
% 27.78/3.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.78/3.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.78/3.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_24570]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_16,negated_conjecture,
% 27.78/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.98      inference(cnf_transformation,[],[f54]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_353,negated_conjecture,
% 27.78/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_16]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_680,plain,
% 27.78/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_4,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 27.78/3.98      inference(cnf_transformation,[],[f43]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_363,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | k3_subset_1(X1_43,X0_43) = k4_xboole_0(X1_43,X0_43) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_4]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_670,plain,
% 27.78/3.98      ( k3_subset_1(X0_43,X1_43) = k4_xboole_0(X0_43,X1_43)
% 27.78/3.98      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_952,plain,
% 27.78/3.98      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_680,c_670]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_5,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 27.78/3.98      inference(cnf_transformation,[],[f44]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_362,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | m1_subset_1(k3_subset_1(X1_43,X0_43),k1_zfmisc_1(X1_43)) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_5]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_671,plain,
% 27.78/3.98      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 27.78/3.98      | m1_subset_1(k3_subset_1(X1_43,X0_43),k1_zfmisc_1(X1_43)) = iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1252,plain,
% 27.78/3.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 27.78/3.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_952,c_671]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_19,plain,
% 27.78/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1523,plain,
% 27.78/3.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.78/3.98      inference(global_propositional_subsumption,
% 27.78/3.98                [status(thm)],
% 27.78/3.98                [c_1252,c_19]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_3,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 27.78/3.98      inference(cnf_transformation,[],[f42]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_364,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | k9_subset_1(X1_43,X0_43,X2_43) = k9_subset_1(X1_43,X2_43,X0_43) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_3]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_669,plain,
% 27.78/3.98      ( k9_subset_1(X0_43,X1_43,X2_43) = k9_subset_1(X0_43,X2_43,X1_43)
% 27.78/3.98      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1540,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),X0_43,k4_xboole_0(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_43) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1523,c_669]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_15,negated_conjecture,
% 27.78/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.98      inference(cnf_transformation,[],[f55]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_354,negated_conjecture,
% 27.78/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_15]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_679,plain,
% 27.78/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_7,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 27.78/3.98      inference(cnf_transformation,[],[f46]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_360,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | k3_subset_1(X1_43,k3_subset_1(X1_43,X0_43)) = X0_43 ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_7]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_673,plain,
% 27.78/3.98      ( k3_subset_1(X0_43,k3_subset_1(X0_43,X1_43)) = X1_43
% 27.78/3.98      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_996,plain,
% 27.78/3.98      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_679,c_673]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_951,plain,
% 27.78/3.98      ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_679,c_670]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1000,plain,
% 27.78/3.98      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = sK2 ),
% 27.78/3.98      inference(light_normalisation,[status(thm)],[c_996,c_951]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_11,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.78/3.98      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
% 27.78/3.98      inference(cnf_transformation,[],[f50]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_356,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | r1_tarski(k3_subset_1(X1_43,X2_43),k3_subset_1(X1_43,k9_subset_1(X1_43,X2_43,X0_43))) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_11]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_677,plain,
% 27.78/3.98      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 27.78/3.98      | m1_subset_1(X2_43,k1_zfmisc_1(X1_43)) != iProver_top
% 27.78/3.98      | r1_tarski(k3_subset_1(X1_43,X2_43),k3_subset_1(X1_43,k9_subset_1(X1_43,X2_43,X0_43))) = iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2551,plain,
% 27.78/3.98      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.78/3.98      | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.78/3.98      | r1_tarski(sK2,k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43))) = iProver_top ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1000,c_677]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_20,plain,
% 27.78/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1203,plain,
% 27.78/3.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 27.78/3.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_951,c_671]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_41641,plain,
% 27.78/3.98      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.78/3.98      | r1_tarski(sK2,k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43))) = iProver_top ),
% 27.78/3.98      inference(global_propositional_subsumption,
% 27.78/3.98                [status(thm)],
% 27.78/3.98                [c_2551,c_20,c_1203]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_41650,plain,
% 27.78/3.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.78/3.98      | r1_tarski(sK2,k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)))) = iProver_top ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1540,c_41641]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1466,plain,
% 27.78/3.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.78/3.98      inference(global_propositional_subsumption,
% 27.78/3.98                [status(thm)],
% 27.78/3.98                [c_1203,c_20]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_10,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.78/3.98      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 27.78/3.98      inference(cnf_transformation,[],[f49]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_357,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | k9_subset_1(X1_43,X2_43,k3_subset_1(X1_43,X0_43)) = k7_subset_1(X1_43,X2_43,X0_43) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_10]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_676,plain,
% 27.78/3.98      ( k9_subset_1(X0_43,X1_43,k3_subset_1(X0_43,X2_43)) = k7_subset_1(X0_43,X1_43,X2_43)
% 27.78/3.98      | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top
% 27.78/3.98      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2353,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),X0_43,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),X0_43,sK1)
% 27.78/3.98      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_680,c_676]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2361,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),X0_43,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),X0_43,sK1)
% 27.78/3.98      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.78/3.98      inference(light_normalisation,[status(thm)],[c_2353,c_952]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_5158,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),sK1) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1466,c_2361]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_9,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 27.78/3.98      inference(cnf_transformation,[],[f48]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_358,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | k7_subset_1(X1_43,X0_43,X2_43) = k4_xboole_0(X0_43,X2_43) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_9]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_675,plain,
% 27.78/3.98      ( k7_subset_1(X0_43,X1_43,X2_43) = k4_xboole_0(X1_43,X2_43)
% 27.78/3.98      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1470,plain,
% 27.78/3.98      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),X0_43) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1466,c_675]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_0,plain,
% 27.78/3.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.78/3.98      inference(cnf_transformation,[],[f39]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_367,plain,
% 27.78/3.98      ( k4_xboole_0(k4_xboole_0(X0_43,X1_43),X2_43) = k4_xboole_0(X0_43,k2_xboole_0(X1_43,X2_43)) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_0]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1475,plain,
% 27.78/3.98      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,X0_43)) ),
% 27.78/3.98      inference(demodulation,[status(thm)],[c_1470,c_367]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_5163,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
% 27.78/3.98      inference(demodulation,[status(thm)],[c_5158,c_1475]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1539,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),X0_43,k4_xboole_0(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X0_43) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1466,c_669]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_5713,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_5163,c_1539]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_41665,plain,
% 27.78/3.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.78/3.98      | r1_tarski(sK2,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)))) = iProver_top ),
% 27.78/3.98      inference(light_normalisation,[status(thm)],[c_41650,c_5713]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2352,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),X0_43,k3_subset_1(u1_struct_0(sK0),sK2)) = k7_subset_1(u1_struct_0(sK0),X0_43,sK2)
% 27.78/3.98      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_679,c_676]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2362,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),X0_43,k4_xboole_0(u1_struct_0(sK0),sK2)) = k7_subset_1(u1_struct_0(sK0),X0_43,sK2)
% 27.78/3.98      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.78/3.98      inference(light_normalisation,[status(thm)],[c_2352,c_951]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_5859,plain,
% 27.78/3.98      ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1523,c_2362]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_5862,plain,
% 27.78/3.98      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
% 27.78/3.98      inference(light_normalisation,[status(thm)],[c_5859,c_5713]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1527,plain,
% 27.78/3.98      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_43) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0_43) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1523,c_675]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1532,plain,
% 27.78/3.98      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_43) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X0_43)) ),
% 27.78/3.98      inference(demodulation,[status(thm)],[c_1527,c_367]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_5863,plain,
% 27.78/3.98      ( k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
% 27.78/3.98      inference(demodulation,[status(thm)],[c_5862,c_1532]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_8,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.78/3.98      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 27.78/3.98      inference(cnf_transformation,[],[f47]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_359,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | k4_subset_1(X1_43,X2_43,X0_43) = k2_xboole_0(X2_43,X0_43) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_8]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_674,plain,
% 27.78/3.98      ( k4_subset_1(X0_43,X1_43,X2_43) = k2_xboole_0(X1_43,X2_43)
% 27.78/3.98      | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top
% 27.78/3.98      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1854,plain,
% 27.78/3.98      ( k4_subset_1(u1_struct_0(sK0),X0_43,sK2) = k2_xboole_0(X0_43,sK2)
% 27.78/3.98      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_679,c_674]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1944,plain,
% 27.78/3.98      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_680,c_1854]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_6,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.78/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.78/3.98      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 27.78/3.98      inference(cnf_transformation,[],[f45]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_361,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
% 27.78/3.98      | m1_subset_1(k4_subset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X1_43)) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_6]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_672,plain,
% 27.78/3.98      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 27.78/3.98      | m1_subset_1(X2_43,k1_zfmisc_1(X1_43)) != iProver_top
% 27.78/3.98      | m1_subset_1(k4_subset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X1_43)) = iProver_top ),
% 27.78/3.98      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2315,plain,
% 27.78/3.98      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 27.78/3.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.78/3.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_1944,c_672]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_10333,plain,
% 27.78/3.98      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.78/3.98      inference(global_propositional_subsumption,
% 27.78/3.98                [status(thm)],
% 27.78/3.98                [c_2315,c_19,c_20]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_10362,plain,
% 27.78/3.98      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_10333,c_673]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_10363,plain,
% 27.78/3.98      ( k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
% 27.78/3.98      inference(superposition,[status(thm)],[c_10333,c_670]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_10364,plain,
% 27.78/3.98      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
% 27.78/3.98      inference(demodulation,[status(thm)],[c_10362,c_10363]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_41666,plain,
% 27.78/3.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.78/3.98      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 27.78/3.98      inference(demodulation,[status(thm)],[c_41665,c_5863,c_10364]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_41676,plain,
% 27.78/3.98      ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
% 27.78/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_41666]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_4346,plain,
% 27.78/3.98      ( r1_tarski(X0_43,X1_43)
% 27.78/3.98      | ~ r1_tarski(k1_tops_1(sK0,X2_43),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X3_43,sK2)))
% 27.78/3.98      | X0_43 != k1_tops_1(sK0,X2_43)
% 27.78/3.98      | X1_43 != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X3_43,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_373]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_11904,plain,
% 27.78/3.98      ( r1_tarski(k1_tops_1(sK0,X0_43),X1_43)
% 27.78/3.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X2_43,sK2)))
% 27.78/3.98      | X1_43 != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X2_43,sK2))
% 27.78/3.98      | k1_tops_1(sK0,X0_43) != k1_tops_1(sK0,sK1) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_4346]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_31346,plain,
% 27.78/3.98      ( r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | k1_tops_1(sK0,X0_43) != k1_tops_1(sK0,sK1)
% 27.78/3.98      | k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_11904]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_31348,plain,
% 27.78/3.98      ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.78/3.98      | k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.78/3.98      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_31346]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_379,plain,
% 27.78/3.98      ( X0_43 != X1_43
% 27.78/3.98      | k1_tops_1(X0_45,X0_43) = k1_tops_1(X0_45,X1_43) ),
% 27.78/3.98      theory(equality) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1012,plain,
% 27.78/3.98      ( X0_43 != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
% 27.78/3.98      | k1_tops_1(sK0,X0_43) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_379]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_10118,plain,
% 27.78/3.98      ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.78/3.98      | k2_xboole_0(sK1,sK2) != k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_1012]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_369,plain,( X0_43 = X0_43 ),theory(equality) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2488,plain,
% 27.78/3.98      ( k2_xboole_0(X0_43,X1_43) = k2_xboole_0(X0_43,X1_43) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_369]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_6614,plain,
% 27.78/3.98      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_2488]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_371,plain,
% 27.78/3.98      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 27.78/3.98      theory(equality) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1165,plain,
% 27.78/3.98      ( X0_43 != X1_43
% 27.78/3.98      | k2_xboole_0(X2_43,X3_43) != X1_43
% 27.78/3.98      | k2_xboole_0(X2_43,X3_43) = X0_43 ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_371]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1890,plain,
% 27.78/3.98      ( X0_43 != k2_xboole_0(X1_43,X2_43)
% 27.78/3.98      | k2_xboole_0(X1_43,X2_43) = X0_43
% 27.78/3.98      | k2_xboole_0(X1_43,X2_43) != k2_xboole_0(X1_43,X2_43) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_1165]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2671,plain,
% 27.78/3.98      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 27.78/3.98      | k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
% 27.78/3.98      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_1890]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2502,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_43,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ r1_tarski(X0_43,k4_subset_1(u1_struct_0(sK0),X1_43,sK2))
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_43,sK2))) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_352]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2504,plain,
% 27.78/3.98      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.78/3.98      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_2502]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2326,plain,
% 27.78/3.98      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_2315]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1922,plain,
% 27.78/3.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_43,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_361]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2253,plain,
% 27.78/3.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_1922]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1,plain,
% 27.78/3.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.78/3.98      inference(cnf_transformation,[],[f40]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_366,plain,
% 27.78/3.98      ( r1_tarski(X0_43,k2_xboole_0(X0_43,X1_43)) ),
% 27.78/3.98      inference(subtyping,[status(esa)],[c_1]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2002,plain,
% 27.78/3.98      ( r1_tarski(X0_43,k2_xboole_0(X0_43,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_366]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_2004,plain,
% 27.78/3.98      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_2002]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_800,plain,
% 27.78/3.98      ( r1_tarski(X0_43,X1_43)
% 27.78/3.98      | ~ r1_tarski(X2_43,k2_xboole_0(X2_43,X3_43))
% 27.78/3.98      | X0_43 != X2_43
% 27.78/3.98      | X1_43 != k2_xboole_0(X2_43,X3_43) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_373]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_882,plain,
% 27.78/3.98      ( r1_tarski(X0_43,k4_subset_1(X1_43,X2_43,X3_43))
% 27.78/3.98      | ~ r1_tarski(X2_43,k2_xboole_0(X2_43,X3_43))
% 27.78/3.98      | X0_43 != X2_43
% 27.78/3.98      | k4_subset_1(X1_43,X2_43,X3_43) != k2_xboole_0(X2_43,X3_43) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_800]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1325,plain,
% 27.78/3.98      ( r1_tarski(X0_43,k4_subset_1(u1_struct_0(sK0),X1_43,sK2))
% 27.78/3.98      | ~ r1_tarski(X1_43,k2_xboole_0(X1_43,sK2))
% 27.78/3.98      | X0_43 != X1_43
% 27.78/3.98      | k4_subset_1(u1_struct_0(sK0),X1_43,sK2) != k2_xboole_0(X1_43,sK2) ),
% 27.78/3.98      inference(instantiation,[status(thm)],[c_882]) ).
% 27.78/3.98  
% 27.78/3.98  cnf(c_1327,plain,
% 27.78/3.98      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.78/3.98      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
% 27.78/3.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 27.78/3.99      | sK1 != sK1 ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_1325]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_1264,plain,
% 27.78/3.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | k4_subset_1(u1_struct_0(sK0),X0_43,sK2) = k2_xboole_0(X0_43,sK2) ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_359]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_1266,plain,
% 27.78/3.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_1264]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_1253,plain,
% 27.78/3.99      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_1252]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_832,plain,
% 27.78/3.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_43
% 27.78/3.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,X0_43) ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_379]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_966,plain,
% 27.78/3.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 27.78/3.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_832]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_12,plain,
% 27.78/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.78/3.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.78/3.99      | ~ l1_pre_topc(X1) ),
% 27.78/3.99      inference(cnf_transformation,[],[f51]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_217,plain,
% 27.78/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.78/3.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.78/3.99      | sK0 != X1 ),
% 27.78/3.99      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_218,plain,
% 27.78/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.99      inference(unflattening,[status(thm)],[c_217]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_351,plain,
% 27.78/3.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | m1_subset_1(k1_tops_1(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.99      inference(subtyping,[status(esa)],[c_218]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_864,plain,
% 27.78/3.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_351]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_805,plain,
% 27.78/3.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_359]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_432,plain,
% 27.78/3.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.78/3.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_351]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_389,plain,
% 27.78/3.99      ( sK1 = sK1 ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_369]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_387,plain,
% 27.78/3.99      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) | sK1 != sK1 ),
% 27.78/3.99      inference(instantiation,[status(thm)],[c_379]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(c_14,negated_conjecture,
% 27.78/3.99      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.78/3.99      inference(cnf_transformation,[],[f56]) ).
% 27.78/3.99  
% 27.78/3.99  cnf(contradiction,plain,
% 27.78/3.99      ( $false ),
% 27.78/3.99      inference(minisat,
% 27.78/3.99                [status(thm)],
% 27.78/3.99                [c_93054,c_79791,c_56697,c_41676,c_31348,c_10118,c_6614,
% 27.78/3.99                 c_2671,c_2504,c_2326,c_2253,c_2004,c_1327,c_1266,c_1253,
% 27.78/3.99                 c_966,c_864,c_805,c_432,c_389,c_387,c_14,c_15,c_16]) ).
% 27.78/3.99  
% 27.78/3.99  
% 27.78/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.78/3.99  
% 27.78/3.99  ------                               Statistics
% 27.78/3.99  
% 27.78/3.99  ------ General
% 27.78/3.99  
% 27.78/3.99  abstr_ref_over_cycles:                  0
% 27.78/3.99  abstr_ref_under_cycles:                 0
% 27.78/3.99  gc_basic_clause_elim:                   0
% 27.78/3.99  forced_gc_time:                         0
% 27.78/3.99  parsing_time:                           0.008
% 27.78/3.99  unif_index_cands_time:                  0.
% 27.78/3.99  unif_index_add_time:                    0.
% 27.78/3.99  orderings_time:                         0.
% 27.78/3.99  out_proof_time:                         0.02
% 27.78/3.99  total_time:                             3.39
% 27.78/3.99  num_of_symbols:                         49
% 27.78/3.99  num_of_terms:                           119407
% 27.78/3.99  
% 27.78/3.99  ------ Preprocessing
% 27.78/3.99  
% 27.78/3.99  num_of_splits:                          0
% 27.78/3.99  num_of_split_atoms:                     0
% 27.78/3.99  num_of_reused_defs:                     0
% 27.78/3.99  num_eq_ax_congr_red:                    26
% 27.78/3.99  num_of_sem_filtered_clauses:            1
% 27.78/3.99  num_of_subtypes:                        3
% 27.78/3.99  monotx_restored_types:                  0
% 27.78/3.99  sat_num_of_epr_types:                   0
% 27.78/3.99  sat_num_of_non_cyclic_types:            0
% 27.78/3.99  sat_guarded_non_collapsed_types:        1
% 27.78/3.99  num_pure_diseq_elim:                    0
% 27.78/3.99  simp_replaced_by:                       0
% 27.78/3.99  res_preprocessed:                       92
% 27.78/3.99  prep_upred:                             0
% 27.78/3.99  prep_unflattend:                        2
% 27.78/3.99  smt_new_axioms:                         0
% 27.78/3.99  pred_elim_cands:                        2
% 27.78/3.99  pred_elim:                              1
% 27.78/3.99  pred_elim_cl:                           1
% 27.78/3.99  pred_elim_cycles:                       3
% 27.78/3.99  merged_defs:                            0
% 27.78/3.99  merged_defs_ncl:                        0
% 27.78/3.99  bin_hyper_res:                          0
% 27.78/3.99  prep_cycles:                            4
% 27.78/3.99  pred_elim_time:                         0.001
% 27.78/3.99  splitting_time:                         0.
% 27.78/3.99  sem_filter_time:                        0.
% 27.78/3.99  monotx_time:                            0.
% 27.78/3.99  subtype_inf_time:                       0.
% 27.78/3.99  
% 27.78/3.99  ------ Problem properties
% 27.78/3.99  
% 27.78/3.99  clauses:                                17
% 27.78/3.99  conjectures:                            3
% 27.78/3.99  epr:                                    0
% 27.78/3.99  horn:                                   17
% 27.78/3.99  ground:                                 3
% 27.78/3.99  unary:                                  5
% 27.78/3.99  binary:                                 6
% 27.78/3.99  lits:                                   36
% 27.78/3.99  lits_eq:                                7
% 27.78/3.99  fd_pure:                                0
% 27.78/3.99  fd_pseudo:                              0
% 27.78/3.99  fd_cond:                                0
% 27.78/3.99  fd_pseudo_cond:                         0
% 27.78/3.99  ac_symbols:                             0
% 27.78/3.99  
% 27.78/3.99  ------ Propositional Solver
% 27.78/3.99  
% 27.78/3.99  prop_solver_calls:                      46
% 27.78/3.99  prop_fast_solver_calls:                 1574
% 27.78/3.99  smt_solver_calls:                       0
% 27.78/3.99  smt_fast_solver_calls:                  0
% 27.78/3.99  prop_num_of_clauses:                    34197
% 27.78/3.99  prop_preprocess_simplified:             65245
% 27.78/3.99  prop_fo_subsumed:                       63
% 27.78/3.99  prop_solver_time:                       0.
% 27.78/3.99  smt_solver_time:                        0.
% 27.78/3.99  smt_fast_solver_time:                   0.
% 27.78/3.99  prop_fast_solver_time:                  0.
% 27.78/3.99  prop_unsat_core_time:                   0.005
% 27.78/3.99  
% 27.78/3.99  ------ QBF
% 27.78/3.99  
% 27.78/3.99  qbf_q_res:                              0
% 27.78/3.99  qbf_num_tautologies:                    0
% 27.78/3.99  qbf_prep_cycles:                        0
% 27.78/3.99  
% 27.78/3.99  ------ BMC1
% 27.78/3.99  
% 27.78/3.99  bmc1_current_bound:                     -1
% 27.78/3.99  bmc1_last_solved_bound:                 -1
% 27.78/3.99  bmc1_unsat_core_size:                   -1
% 27.78/3.99  bmc1_unsat_core_parents_size:           -1
% 27.78/3.99  bmc1_merge_next_fun:                    0
% 27.78/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.78/3.99  
% 27.78/3.99  ------ Instantiation
% 27.78/3.99  
% 27.78/3.99  inst_num_of_clauses:                    2956
% 27.78/3.99  inst_num_in_passive:                    926
% 27.78/3.99  inst_num_in_active:                     3877
% 27.78/3.99  inst_num_in_unprocessed:                923
% 27.78/3.99  inst_num_of_loops:                      4127
% 27.78/3.99  inst_num_of_learning_restarts:          1
% 27.78/3.99  inst_num_moves_active_passive:          238
% 27.78/3.99  inst_lit_activity:                      0
% 27.78/3.99  inst_lit_activity_moves:                0
% 27.78/3.99  inst_num_tautologies:                   0
% 27.78/3.99  inst_num_prop_implied:                  0
% 27.78/3.99  inst_num_existing_simplified:           0
% 27.78/3.99  inst_num_eq_res_simplified:             0
% 27.78/3.99  inst_num_child_elim:                    0
% 27.78/3.99  inst_num_of_dismatching_blockings:      18065
% 27.78/3.99  inst_num_of_non_proper_insts:           17235
% 27.78/3.99  inst_num_of_duplicates:                 0
% 27.78/3.99  inst_inst_num_from_inst_to_res:         0
% 27.78/3.99  inst_dismatching_checking_time:         0.
% 27.78/3.99  
% 27.78/3.99  ------ Resolution
% 27.78/3.99  
% 27.78/3.99  res_num_of_clauses:                     28
% 27.78/3.99  res_num_in_passive:                     28
% 27.78/3.99  res_num_in_active:                      0
% 27.78/3.99  res_num_of_loops:                       96
% 27.78/3.99  res_forward_subset_subsumed:            665
% 27.78/3.99  res_backward_subset_subsumed:           18
% 27.78/3.99  res_forward_subsumed:                   0
% 27.78/3.99  res_backward_subsumed:                  0
% 27.78/3.99  res_forward_subsumption_resolution:     0
% 27.78/3.99  res_backward_subsumption_resolution:    0
% 27.78/3.99  res_clause_to_clause_subsumption:       14427
% 27.78/3.99  res_orphan_elimination:                 0
% 27.78/3.99  res_tautology_del:                      1957
% 27.78/3.99  res_num_eq_res_simplified:              0
% 27.78/3.99  res_num_sel_changes:                    0
% 27.78/3.99  res_moves_from_active_to_pass:          0
% 27.78/3.99  
% 27.78/3.99  ------ Superposition
% 27.78/3.99  
% 27.78/3.99  sup_time_total:                         0.
% 27.78/3.99  sup_time_generating:                    0.
% 27.78/3.99  sup_time_sim_full:                      0.
% 27.78/3.99  sup_time_sim_immed:                     0.
% 27.78/3.99  
% 27.78/3.99  sup_num_of_clauses:                     5039
% 27.78/3.99  sup_num_in_active:                      780
% 27.78/3.99  sup_num_in_passive:                     4259
% 27.78/3.99  sup_num_of_loops:                       824
% 27.78/3.99  sup_fw_superposition:                   3136
% 27.78/3.99  sup_bw_superposition:                   4245
% 27.78/3.99  sup_immediate_simplified:               3206
% 27.78/3.99  sup_given_eliminated:                   2
% 27.78/3.99  comparisons_done:                       0
% 27.78/3.99  comparisons_avoided:                    0
% 27.78/3.99  
% 27.78/3.99  ------ Simplifications
% 27.78/3.99  
% 27.78/3.99  
% 27.78/3.99  sim_fw_subset_subsumed:                 9
% 27.78/3.99  sim_bw_subset_subsumed:                 1
% 27.78/3.99  sim_fw_subsumed:                        404
% 27.78/3.99  sim_bw_subsumed:                        33
% 27.78/3.99  sim_fw_subsumption_res:                 0
% 27.78/3.99  sim_bw_subsumption_res:                 0
% 27.78/3.99  sim_tautology_del:                      0
% 27.78/3.99  sim_eq_tautology_del:                   647
% 27.78/3.99  sim_eq_res_simp:                        0
% 27.78/3.99  sim_fw_demodulated:                     1630
% 27.78/3.99  sim_bw_demodulated:                     93
% 27.78/3.99  sim_light_normalised:                   1358
% 27.78/3.99  sim_joinable_taut:                      0
% 27.78/3.99  sim_joinable_simp:                      0
% 27.78/3.99  sim_ac_normalised:                      0
% 27.78/3.99  sim_smt_subsumption:                    0
% 27.78/3.99  
%------------------------------------------------------------------------------
